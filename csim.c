/* Name: Aksel Torgerson
 * CS login: aksel
 * Section(s): Lecture 2
 *
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss plus a possible eviction.
 *  2. Instruction loads (I) are ignored.
 *  3. Data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus a possible eviction.
 *
 * The function print_summary() is given to print output.
 * Please use this function to print the number of hits, misses and evictions.
 * This is crucial for the driver to evaluate your work. 
 */

#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include <stdbool.h>

/****************************************************************************/
/***** DO NOT MODIFY THESE VARIABLE NAMES ***********************************/

/* Globals set by command line args */
int s = 0; /* set index bits */
int E = 0; /* associativity */
int b = 0; /* block offset bits */
int verbosity = 0; /* print trace if set */
char* trace_file = NULL;

/* Derived from command line args */
int B; /* block size (bytes) B = 2^b */
int S; /* number of sets S = 2^s In C, you can use the left shift operator */

/* Counters used to record cache statistics */
int hit_cnt = 0;
int miss_cnt = 0;
int evict_cnt = 0;
/*****************************************************************************/

/* Type: Memory address 
 * Use this type whenever dealing with addresses or address masks
 */                    
typedef unsigned long long int mem_addr_t;

/* Type: Cache line 
 * 
 * NOTE: 
 * You might (not necessarily though) want to add an extra field to this struct
 * depending on your implementation
 * 
 * For example, to use a linked list based LRU,
 * you might want to have a field "struct cache_line * next" in the struct 
 */                    
typedef struct cache_line {
    long counter;    
    char valid;
    mem_addr_t tag;
} cache_line_t;

typedef cache_line_t* cache_set_t;
typedef cache_set_t* cache_t;


/* The cache we are simulating */
cache_t cache;  

/*
 * init_cache - 
 * Allocate data structures to hold info regrading the sets and cache lines
 * use struct "cache_line_t" here
 * Initialize valid and tag field with 0s.
 * use S (= 2^s) and E while allocating the data structures here
 */
void init_cache() {
    S = 2 << (s - 1);  // 2^s
    B = 2 << (b - 1);  // 2^b
    // allocate S number of cache_set types
    cache = malloc(S * sizeof(cache_set_t));
    // check the return value
    if (cache == NULL){
        printf("Malloc did not successfully allocate data to the cache");
        exit(1);
    }
    // loop through the number of sets we have, allocate a line for each one
    for (int i = 0; i < S; i++) {
        cache[i] = malloc(E * sizeof(cache_line_t));
        // check return value again
        if (cache[i] == NULL){
            printf("Malloc did not successfully allocate data to the cache");
            exit(1);
        }
        // for each of the lines we allocated set the initial values to 0
        for (int j = 0; j < E; j++){
            cache[i][j].counter = 0;
            cache[i][j].valid = '0';
            cache[i][j].tag = 0;
        }
    }    
}

/*  
 * free_cache - free each piece of memory you allocated using malloc 
 * inside init_cache() function
 */                    
void free_cache() {
    // free each of the set arrays
    for (int i = 0; i < S; i++){
        free(cache[i]);
        cache[i] = NULL;
    }
    // free the cache array and make sure to set pointers to NULL
    free(cache);
    cache = NULL;
}

/* 
 * access_data - Access data at memory address addr.
 *   If it is already in cache, increase hit_cnt
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Also increase evict_cnt if a line is evicted.
 *   you will manipulate data structures allocated in init_cache() here
 */                    
void access_data(mem_addr_t addr) {
    // do some binary extraction to get the correct bits from the address 
    mem_addr_t tag = addr >> (s + b);
    mem_addr_t set = (addr - (tag << (s + b))) >> b;
    // declare some pointer varaibles to use while accessing data
    cache_line_t *mru_line, *lru_line, *empty_line, *hit_line;
    mru_line = &cache[set][0];
    lru_line = &cache[set][0];
    hit_line = NULL;
    empty_line = NULL;
    // we already know the set so just loop through the lines
    for (int i = 0; i < E; i++) {
        // if the tag is valid, otherwise note that it is in empty line
        if (cache[set][i].valid == '1'){
            // if the tag equals the tag we want we get a hit
            if (cache[set][i].tag == tag){
                hit_line = &cache[set][i];  // update hit_line pointer
            }
            // keep track of our MRU and LRU lines by updating the pointer
            if (cache[set][i].counter > mru_line->counter) {
                mru_line = &cache[set][i];
            }    
            if (cache[set][i].counter < lru_line->counter) {
                lru_line = &cache[set][i];
            }
        } else {
            // since the valid bit was not '1' we denote an empty line here
            empty_line = &cache[set][i];
        }
    }

    // if the hit pointer is not null then we are good to go
    if (hit_line != NULL) {
        hit_line->counter = mru_line->counter + 1;  // update the counter val
        hit_cnt++;  // increase our hit count
    } else if (empty_line != NULL) {  // if its empty line, no eviction needed
        empty_line->valid = '1';  // update empty line data
        empty_line->tag = tag;  // set tag
        empty_line->counter = mru_line->counter + 1;  // update the counter val
        miss_cnt++;
        // else if its not a hit or a cold miss, must be a conflict miss
    } else {
        lru_line->valid = '1';  // update the block thats being evicted
        lru_line->tag = tag;  // update tag
        lru_line->counter = mru_line->counter + 1;  // increase the counter
        miss_cnt++;
        evict_cnt++;
    }
}

/* 
 * replay_trace - replays the given trace file against the cache 
 * reads the input trace file line by line
 * extracts the type of each memory access : L/S/M
 * YOU MUST TRANSLATE one "L" as a load i.e. 1 memory access
 * YOU MUST TRANSLATE one "S" as a store i.e. 1 memory access
 * YOU MUST TRANSLATE one "M" as a load followed by a store i.e. 2 memory accesses
 */                    
void replay_trace(char* trace_fn) {                      
    char buf[1000];
    mem_addr_t addr = 0;
    unsigned int len = 0;
    FILE* trace_fp = fopen(trace_fn, "r");

    if (!trace_fp) {
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);
    }

    while (fgets(buf, 1000, trace_fp) != NULL) {
        if (buf[1] == 'S' || buf[1] == 'L' || buf[1] == 'M') {
            sscanf(buf+3, "%llx,%u", &addr, &len);
      
            if (verbosity)
                printf("%c %llx,%u ", buf[1], addr, len);

        access_data(addr);  // do a data access
        if (buf[1] == 'M') {  // if its modify, we need to access mem twice
            (access_data(addr));
        }

            if (verbosity)
                printf("\n");
        }
    }

    fclose(trace_fp);
}

/*
 * print_usage - Print usage info
 */                    
void print_usage(char* argv[]) {                 
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}

/*
 * print_summary - Summarize the cache simulation statistics. Student cache simulators
 *                must call this function in order to be properly autograded.
 */                    
void print_summary(int hits, int misses, int evictions) {                
    printf("hits:%d misses:%d evictions:%d\n", hits, misses, evictions);
    FILE* output_fp = fopen(".csim_results", "w");
    assert(output_fp);
    fprintf(output_fp, "%d %d %d\n", hits, misses, evictions);
    fclose(output_fp);
}

/*
 * main - Main routine 
 */                    
int main(int argc, char* argv[]) {                      
    char c;
    
    // Parse the command line arguments: -h, -v, -s, -E, -b, -t 
    while ((c = getopt(argc, argv, "s:E:b:t:vh")) != -1) {
        switch (c) {
            case 'b':
                b = atoi(optarg);
                break;
            case 'E':
                E = atoi(optarg);
                break;
            case 'h':
                print_usage(argv);
                exit(0);
            case 's':
                s = atoi(optarg);
                break;
            case 't':
                trace_file = optarg;
                break;
            case 'v':
                verbosity = 1;
                break;
            default:
                print_usage(argv);
                exit(1);
        }
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        print_usage(argv);
        exit(1);
    }

    /* Initialize cache */
    init_cache();

    replay_trace(trace_file);

    /* Free allocated memory */
    free_cache();

    /* Output the hit and miss statistics for the autograder */
    print_summary(hit_cnt, miss_cnt, evict_cnt);
    return 0;
}
