/*
Yarýn: onePath hakkýndaki assumelarý falan kaldýr. Bu dosyayý yedekle. localGrid'i pointer deðil array olarak tanýmla. Bir de öyle dene invariantlarý.
*/

#include <vcc.h>
#include <limits.h>
#include<stdlib.h>

#define WIDTH 10
#define MAX_POINTS 10
#define MAX_PATHS 5

typedef struct Int Int, *PInt;
typedef struct Grid Grid, *PGrid;
typedef struct Path Path, *PPath;
typedef struct PathList PathList, *PPathList;
typedef struct RwLock RwLock, *PRwLock;
typedef struct PSpan PSpan, *PPSpan;

struct Path{
	unsigned xs[MAX_POINTS];
	unsigned ID;
	unsigned path_len;

//_(invariant \mine((int [MAX_POINTS]) xs))
	_(invariant path_len<= MAX_POINTS)
	_(invariant ID<MAX_PATHS)
	_(invariant (int) (ID) != -1)
	//_(invariant \forall int i; i>=path_len && i<MAX_POINTS ==> xs[i] == -1)
	//_(invariant \forall int i; i>=0 && i<path_len ==> xs[i]>=0 && xs[i] <WIDTH)
};

/*_(dynamic_owns) */struct PathList{
	PPath pathlist[MAX_PATHS];
	unsigned num_paths;
	//_(invariant \forall unsigned i; i<num_paths ==> \mine(pathlist[i]))
	_(invariant num_paths<MAX_PATHS)
	//_(invariant \mine((PPath [MAX_PATHS]) pathlist))
	_(invariant \forall unsigned i,j; i<num_paths && j<num_paths ==> i!=j ==> pathlist[i] != pathlist[j])
};

struct Int{
	int data;
};

struct Grid{
	PRwLock gridPoints[WIDTH];
	_(invariant \forall unsigned i,j; i != j && i<WIDTH && j<WIDTH ==> gridPoints[i] != gridPoints[j])
};

_(logic \bool isEqual(unsigned x1, unsigned x2) = x1 == x2)
_(logic \bool isAdjacent(unsigned x1, unsigned x2) = _(unchecked) (x1-x2) == 1 || _(unchecked) (x2 -x1) == 1)
_(logic \bool isAdjacentPath(PPath path) = \forall unsigned i; i<path->path_len-1 ==> isAdjacent(path->xs[i],path->xs[i+1]))
_(logic \bool isValidPath(PPath path, PInt grid) = \forall unsigned i; i<path->path_len ==> grid[path->xs[i] ].data == (int) path->ID)
_(logic \bool isValidPath(PPath path, PGrid grid) = \forall unsigned i; i<path->path_len ==> grid->gridPoints[path->xs[i]]->resource->data == (int) path->ID)

/*{xchg}*/
_(atomic_inline) unsigned InterlockedCompareExchange(volatile unsigned *Destination, unsigned Exchange, unsigned Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}
_(ghost struct Token {
  int dummy;
})
_(ghost _(claimable) struct Counter {
  int dummy;
})

_(volatile_owns)
struct PSpan {
  volatile unsigned cnt;
  PPathList resource;
  _(invariant \mine(&claim_counter))
  _(invariant (&claim_counter)->\claim_count == cnt >> 1)
  _(invariant \on_unwrap(\this, (&claim_counter)->\claim_count == 0))

  _(ghost struct Token token)
  _(ghost struct Counter claim_counter)
  _(invariant (cnt & 1) == 0 ==> \mine(&token))
  _(invariant (cnt != 1) ==> \mine(resource))
  _(invariant \mine(&token) || \mine(resource))
};


/*{refcnt}*/
_(volatile_owns)
struct RwLock {
  volatile unsigned cnt;
  PInt resource;
  _(invariant \mine(&claim_counter))
  _(invariant (&claim_counter)->\claim_count == cnt >> 1)
  _(invariant \on_unwrap(\this, (&claim_counter)->\claim_count == 0))

  _(ghost struct Token token)
  _(ghost struct Counter claim_counter)
  _(invariant (cnt & 1) == 0 ==> \mine(&token))
  _(invariant (cnt != 1) ==> \mine(resource))
  _(invariant \mine(&token) || \mine(resource))
};

/*{incr}*/
void acquire_read(struct RwLock *r _(ghost \claim c)
             _(out \claim ret))
  _(always c, r->\closed)
  _(ensures \claims_object(ret, &r->claim_counter) && \claims(ret, r->resource->\closed) && \wrapped0(ret) && \fresh(ret))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) continue;

    _(assume v <= UINT_MAX - 2)
    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v + 2, v);
      _(ghost
        if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0 && r->resource->\closed))
       // if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0))
    }

    if (v == n) return;
  }
}

void acquire_read(struct PSpan *r _(ghost \claim c)
             _(out \claim ret))
  _(always c, r->\closed)
  _(ensures \claims_object(ret, &r->claim_counter) && \claims(ret, r->resource->\closed) && \wrapped0(ret) && \fresh(ret))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) continue;

    _(assume v <= UINT_MAX - 2)
    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v + 2, v);
      _(ghost
        if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0 && r->resource->\closed))
       // if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0))
    }

    if (v == n) return;
  }
}
/*{decr}*/
void release_read(struct RwLock *r _(ghost \claim c) _(ghost \claim handle))
  _(always c, r->\closed)
  _(requires \claims_object(handle, &r->claim_counter) && \wrapped0(handle))
  _(requires c != handle)
  _(writes handle)
{
  unsigned v, n;

  for (;;)
    _(invariant \wrapped(c) && \wrapped0(handle))
  {
    _(atomic c, r) {
      v = r->cnt;
      _(assert \active_claim(handle))
      _(assert v >= 2)
    }

    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v - 2, v);
      _(ghost
        if (v == n) {
          \destroy_claim(handle, {&r->claim_counter});
        })
    }

    if (v == n) break;
  }
}

void release_read(struct PSpan *r _(ghost \claim c) _(ghost \claim handle))
  _(always c, r->\closed)
  _(requires \claims_object(handle, &r->claim_counter) && \wrapped0(handle))
  _(requires c != handle)
  _(writes handle)
{
  unsigned v, n;

  for (;;)
    _(invariant \wrapped(c) && \wrapped0(handle))
  {
    _(atomic c, r) {
      v = r->cnt;
      _(assert \active_claim(handle))
      _(assert v >= 2)
    }

    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v - 2, v);
      _(ghost
        if (v == n) {
          \destroy_claim(handle, {&r->claim_counter});
        })
    }

    if (v == n) break;
  }
}
void acquire_write(struct RwLock *r _(ghost \claim c))
  _(always c, r->\closed)
  _(ensures \wrapped(&r->token) && \fresh(&r->token))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) continue;

    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v|1, v);
      _(ghost
        if (v == n) {
          r->\owns -= &r->token;
        })
    }

    if (v == n) break;
  }
}

void acquire_write(struct PSpan *r _(ghost \claim c))
  _(always c, r->\closed)
  _(ensures \wrapped(&r->token) && \fresh(&r->token))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) continue;

    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v|1, v);
      _(ghost
        if (v == n) {
          r->\owns -= &r->token;
        })
    }

    if (v == n) break;
  }
}

void acquire_commit(struct RwLock *r _(ghost \claim c))
_(always c, r->\closed)
_(requires \wrapped(&r->token))
_(writes &r->token)
_(ensures \wrapped(r->resource) && \fresh(r->resource))
{
  unsigned v,n;
  for (;;)
    _(invariant \wrapped(&r->token))
    _(writes &r->token)
  {
    _(atomic c, r) {
      v = r->cnt;
      _(ghost
        if (v == 1) {
          r->\owns += &r->token;
          r->\owns -= r->resource;
        })
    }
    if (v == 1) break;
  }
}

void acquire_commit(struct PSpan *r _(ghost \claim c))
_(always c, r->\closed)
_(requires \wrapped(&r->token))
_(writes &r->token)
_(ensures \wrapped(r->resource) && \fresh(r->resource))
{
  unsigned v,n;
  for (;;)
    _(invariant \wrapped(&r->token))
    _(writes &r->token)
  {
    _(atomic c, r) {
      v = r->cnt;
      _(ghost
        if (v == 1) {
          r->\owns += &r->token;
          r->\owns -= r->resource;
        })
    }
    if (v == 1) break;
  }
}

void release_write(struct RwLock *r _(ghost \claim c))
  _(always c, r->\closed)
  //_(requires c != r->resource)
  _(requires \wrapped(r->resource))
  _(writes r->resource)
{
  _(atomic c, r) {
    r->cnt = 0;
    _(ghost r->\owns += r->resource)
  }
}

void release_write(struct PSpan *r _(ghost \claim c))
  _(always c, r->\closed)
  //_(requires c != r->resource)
  _(requires \wrapped(r->resource))
  _(writes r->resource)
{
  _(atomic c, r) {
    r->cnt = 0;
    _(ghost r->\owns += r->resource)
  }
}

PPath shortestPath(PInt grid, unsigned x1, unsigned x2)
_(maintains \forall unsigned i; i<WIDTH ==> \wrapped(grid+i))
_(ensures \wrapped(\result) && \fresh(\result))
_(ensures \result->path_len < MAX_POINTS)
_(ensures \forall unsigned i; i<MAX_POINTS ==> \result->xs[i]<WIDTH && \result->xs[i]>=0)
_(ensures isValidPath(\result, grid) && isAdjacentPath(\result) && isEqual(x1,\result->xs[0]) && isEqual(x2,\result->xs[\result->path_len-1]))
//_(ensures \forall unsigned i; i<\result->path_len ==> grid[\result->xs[i] ].data == (int) \result->ID)
	;
void readGrid(PGrid grid, PPSpan pathlist, unsigned x1, unsigned x2 _(ghost \claim c))
_(always c, grid->\closed && pathlist->\closed && (\forall unsigned j; j<WIDTH ==> grid->gridPoints[j]->\closed && grid->gridPoints[j]->resource == \when_claimed( grid->gridPoints[j]->resource))
		&& (\forall unsigned i,j; i != j && i<WIDTH && j<WIDTH ==> grid->gridPoints[i]->resource != grid->gridPoints[j]->resource))
_(requires x1>=0 && x2>=0 && x1<=WIDTH && x2 <= WIDTH && x1<x2)
//_(writes *s)
{
	/*unsigned i,v;
	int a;
	PInt tempint;
	PRwLock p;
	PPath onePath;
	PPathList localPathList;
	PPathList tempList;
	_(ghost \claim cxx)
	localPathList = malloc(sizeof(PathList));
	_(assume localPathList)

	PInt localGrid= malloc(sizeof(Int)*WIDTH);
	_(assume localGrid)
	_(assume \forall unsigned i; i<WIDTH ==> localGrid != grid->gridPoints[i]->resource)
	
	for(i=0; i<WIDTH; i++)
	_(writes \array_range(localGrid,WIDTH))
	_(invariant \mutable_array(localGrid,WIDTH))
	{
		_(ghost \claim cx)
		acquire_read(grid->gridPoints[i] _(ghost c) _(out cx));
		_(atomic c, cx, _(read_only) grid->gridPoints[i]->resource, _(read_only) grid->gridPoints[i], _(read_only) grid){
			_(assume \forall unsigned j; j<i ==> grid->gridPoints[j]->resource->data == localGrid[i].data)
			localGrid[i].data = grid->gridPoints[i]->resource->data;
		}
		release_read(grid->gridPoints[i] _(ghost c) _(ghost cx));
	}

	for(i=0;i<WIDTH; i++)
	_(invariant \writable(localPathList->pathlist))
	_(invariant \forall unsigned j; j<WIDTH && j>= i ==> \writable(localGrid+j) && \mutable(localGrid+j))
	_(invariant \forall unsigned j;  j<i ==> \wrapped(localGrid+j) )
	{
		_(wrap localGrid+i)
	}

	_(atomic c, pathlist){
		tempList = pathlist->resource;
	}

	acquire_read(pathlist _(ghost c) _(out cxx));
	
	for(i=0; i<MAX_PATHS;i++)
	_(invariant \wrapped0(cxx) && \forall unsigned j; j<WIDTH ==> \wrapped( localGrid+j ))
	_(invariant \writable(cxx) && \writable(localPathList))
	{
		_(atomic cxx, _(read_only) tempList){
			_(assume \forall unsigned j; j<WIDTH ==> grid->gridPoints[j]->resource->data == localGrid[j].data)
			localPathList->pathlist[i] = tempList->pathlist[i];
		}
	}
	release_read(pathlist _(ghost c) _(ghost cxx));
	
	onePath = shortestPath(localGrid, x1,x2);
	acquire_write(pathlist _(ghost c));

	_(assert \wrapped(onePath) && \forall unsigned i; i<WIDTH ==> \wrapped(localGrid+i))
	_(assert isValidPath(onePath, localGrid))
	acquire_commit(pathlist _(ghost c));
	_(unwrap pathlist->resource)

	//_(assert ((int [MAX_POINTS]) onePath->xs) \in onePath->\owns)
	//_(assume \forall unsigned i; i<WIDTH ==> localGrid != grid->gridPoints[i]->resource)
	for(i=0; i < onePath->path_len;i++)
	_(invariant \wrapped(onePath) && \forall unsigned j; j<WIDTH ==> \wrapped(localGrid+j))
	_(invariant onePath->path_len <= MAX_POINTS)
	_(invariant \forall unsigned j; j<onePath->path_len ==> onePath->xs[j]<WIDTH && onePath->xs[j]>=0)
	_(invariant \forall unsigned j; j<i ==> \mutable(grid->gridPoints[onePath->xs[j]]->resource))
	_(invariant \forall unsigned j; j<i ==> \writable(grid->gridPoints[onePath->xs[j]]->resource))
	_(invariant \writable(pathlist->resource))
	_(invariant \mutable(pathlist->resource))
	_(invariant \forall unsigned i; i<WIDTH ==> localGrid != grid->gridPoints[i]->resource)
	_(invariant isValidPath(onePath, localGrid))
	_(invariant isAdjacentPath(onePath) && isEqual(x1,onePath->xs[0]) && isEqual(x2,onePath->xs[onePath->path_len-1]))
	{
		acquire_write(grid->gridPoints[onePath->xs[i]] _(ghost c));
		acquire_commit(grid->gridPoints[onePath->xs[i]] _(ghost c));
		_(unwrap grid->gridPoints[onePath->xs[i]]->resource) 
	}
	_(assert isValidPath(onePath, localGrid) && isAdjacentPath(onePath) && isEqual(x1,onePath->xs[0]) && isEqual(x2,onePath->xs[onePath->path_len-1]))

	_(assert \mutable(pathlist->resource) && \writable(pathlist->resource))
	_(assert \forall unsigned i; i<onePath->path_len ==> \mutable(grid->gridPoints[onePath->xs[i]]->resource) && \writable(grid->gridPoints[onePath->xs[i]]->resource))*/
	//Do the writing and verify specs...

	/*_(assume \forall unsigned i; i<onePath->path_len ==> grid->gridPoints[onePath->xs[i]]->resource->data == -1)
	_(assume pathlist->resource->num_paths >0 && onePath->path_len >0)
	_(assume \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==>  \forall unsigned i; i<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[i]]->resource->data == (int) pathlist->resource->pathlist[j]->ID)

	_(assert \forall unsigned k;{pathlist->resource->pathlist[k]} k<pathlist->resource->num_paths ==> \forall unsigned i,j; i<pathlist->resource->pathlist[k]->path_len && j<onePath->path_len ==> pathlist->resource->pathlist[k]->xs[i] != onePath->xs[j])
	
	for(i=0; i<onePath->path_len;i++)
	_(invariant \wrapped(onePath))
	_(invariant \active_claim(c))
	_(invariant onePath->path_len <= MAX_POINTS)
	_(invariant \forall unsigned j; j<onePath->path_len ==> onePath->xs[j]<WIDTH && onePath->xs[j]>=0)
	_(invariant \forall unsigned i; i<onePath->path_len ==> \mutable(grid->gridPoints[onePath->xs[i]]->resource) && \writable(grid->gridPoints[onePath->xs[i]]->resource))
	{
		_(atomic c, _(read_only) grid, _(read_only) grid->gridPoints[onePath->xs[i]]){
			tempint = grid->gridPoints[onePath->xs[i]]->resource;
		}
		_(assume onePath->ID < MAX_PATHS)
		tempint->data = (int) onePath->ID;
	}*/
	
	//_(assert \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==>  \forall unsigned i; i<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[i]]->resource->data == (int) pathlist->resource->pathlist[j]->ID)
	/*_(assert \forall unsigned i; i<onePath->path_len ==> \mutable(grid->gridPoints[onePath->xs[i]]->resource))
	_(assert \forall unsigned i; i<onePath->path_len ==> onePath->xs[i]>=0 && onePath->xs[i] < WIDTH)
	_(assert \active_claim(c) && \forall unsigned i,j; i != j && i<WIDTH && j<WIDTH ==> grid->gridPoints[i]->resource != grid->gridPoints[j]->resource)
	_(assume \active_claim(c) && \forall unsigned i,j; i != j && i<onePath->path_len && j<onePath->path_len ==> grid->gridPoints[onePath->xs[i]]->resource != grid->gridPoints[onePath->xs[j]]->resource)
	
	for(i=0; i<onePath->path_len; i++)
	_(invariant \wrapped(onePath))
	_(invariant \forall unsigned j; j>=i && j<onePath->path_len ==> \mutable(grid->gridPoints[onePath->xs[j]]->resource))
	_(invariant \forall unsigned j; j>=i && j<onePath->path_len ==> \writable(grid->gridPoints[onePath->xs[j]]->resource))
	_(invariant \forall unsigned i,j; i != j && i<onePath->path_len && j<onePath->path_len ==> grid->gridPoints[onePath->xs[i]]->resource != grid->gridPoints[onePath->xs[j]]->resource)
	_(invariant \writable(pathlist->resource))
	_(invariant \mutable(pathlist->resource))
	{
		_(wrap grid->gridPoints[onePath->xs[i]]->resource)
		_(assume \active_claim(c) && \forall unsigned i,j; i != j && i<onePath->path_len && j<onePath->path_len ==> grid->gridPoints[onePath->xs[i]]->resource != grid->gridPoints[onePath->xs[j]]->resource)
	}

	_(assert \writable(pathlist->resource))
	_(assert \mutable(pathlist->resource))
	_(wrap pathlist->resource)*/
	//_(assert \false)
}

void writeGrid(PGrid grid, PPSpan pathlist, unsigned x1, unsigned x2,PPath onePath _(ghost \claim c))
_(always c, grid->\closed && pathlist->\closed && (\forall unsigned j; j<WIDTH ==> grid->gridPoints[j]->\closed && grid->gridPoints[j]->resource == \when_claimed( grid->gridPoints[j]->resource))
		&& (\forall unsigned i,j; i != j && i<WIDTH && j<WIDTH ==> grid->gridPoints[i]->resource != grid->gridPoints[j]->resource))
_(requires x1>=0 && x2>=0 && x1<=WIDTH && x2 <= WIDTH && x1<x2)
_(requires \wrapped(onePath))
/*_(requires \mutable(pathlist->resource) )
_(requires \mutable(pathlist->resource->pathlist))
_(writes pathlist->resource->pathlist[pathlist->resource->num_paths]) */
_(requires \wrapped(pathlist->resource))
_(requires \forall unsigned i; i<onePath->path_len ==> \wrapped(grid->gridPoints[onePath->xs[i]]->resource) )
_(requires onePath->path_len <= MAX_POINTS)
_(requires \forall unsigned j; j<onePath->path_len ==> onePath->xs[j]<WIDTH && onePath->xs[j]>=0)
_(requires \forall unsigned i; i<pathlist->resource->num_paths ==> pathlist->resource->pathlist[i] != onePath)
_(requires \forall unsigned j,k; j<onePath->path_len && k<onePath->path_len && j != k ==> onePath->xs[j] != onePath->xs[k])
_(writes pathlist->resource)
{
	unsigned i;
	PInt tempint;
	PInt writeSet[MAX_POINTS];
	_(ghost \claim cxx)

	for(i=0; i<onePath->path_len; i++)
	_(invariant \active_claim(c))
	_(invariant \mutable_array(writeSet,onePath->path_len))
	_(writes \array_range(writeSet,onePath->path_len))
	_(invariant \forall unsigned i; i<onePath->path_len ==> \wrapped(grid->gridPoints[onePath->xs[i]]->resource))
	_(invariant \forall unsigned j; j<i ==>  writeSet[j] == grid->gridPoints[onePath->xs[j]]->resource)
	_(invariant \forall unsigned k,j; k<i && j<i && k != j ==> writeSet[k] != writeSet[j])
	_(invariant \forall unsigned j; j<onePath->path_len ==> onePath->xs[j]<WIDTH && onePath->xs[j]>=0)
	_(invariant \forall unsigned k,j; k<WIDTH && j<WIDTH && k != j ==> grid->gridPoints[k]->resource != grid->gridPoints[j]->resource) 
	_(invariant \forall unsigned j,k; j<onePath->path_len && k<onePath->path_len && j != k ==> onePath->xs[j] != onePath->xs[k])
	{
		_(atomic c, _(read_only) grid, _(read_only) grid->gridPoints[onePath->xs[i]]){
			writeSet[i] = grid->gridPoints[onePath->xs[i]]->resource;
		}
	}
	_(assert \forall unsigned i; i<onePath->path_len ==> writeSet[i] == grid->gridPoints[onePath->xs[i]]->resource)
	_(assert \forall unsigned i; i<onePath->path_len ==> \wrapped(writeSet[i]))
	_(assert \forall unsigned i,j; i<onePath->path_len && j<onePath->path_len && i != j ==> writeSet[i] != writeSet[j])
	
	
	for(i=0; i<onePath->path_len; i++)
	_(invariant \wrapped(onePath))
	_(invariant \forall unsigned j; j<onePath->path_len ==>  writeSet[j] == grid->gridPoints[onePath->xs[j]]->resource)
	_(invariant \forall unsigned j; j>=i && j<onePath->path_len ==> \wrapped(writeSet[j]))
	_(invariant \forall unsigned j; j<i ==> \mutable(writeSet[j]))
	_(invariant \forall unsigned k,j; k<onePath->path_len && j<onePath->path_len && k != j ==> writeSet[k] != writeSet[j])
	_(invariant \thread_local_array(writeSet, onePath->path_len))
	_(writes \array_range(writeSet,onePath->path_len))
	{
		_(assume \writable(writeSet[i]))
		_(unwrap writeSet[i])
	}
	
	_(assume \forall unsigned i; i<onePath->path_len ==> grid->gridPoints[onePath->xs[i]]->resource->data == -1)
	_(assume \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==>  \forall unsigned i; i<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[i]]->resource->data == (int) pathlist->resource->pathlist[j]->ID)

	_(assert \forall unsigned k;{pathlist->resource->pathlist[k]} k<pathlist->resource->num_paths ==> \forall unsigned i,j; i<pathlist->resource->pathlist[k]->path_len && j<onePath->path_len ==> pathlist->resource->pathlist[k]->xs[i] != onePath->xs[j])
	_(assert \forall unsigned i; {writeSet[i]} i<onePath->path_len ==> \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==> \forall unsigned k; k<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[k]]->resource != writeSet[i])

	for(i=0; i<onePath->path_len;i++)
	_(invariant \wrapped(onePath))
	_(invariant \thread_local_array(writeSet, onePath->path_len))
	_(invariant onePath->path_len <= MAX_POINTS)
	_(invariant \forall unsigned j; j<onePath->path_len ==> onePath->xs[j]<WIDTH && onePath->xs[j]>=0)
	_(invariant \forall unsigned j; j<onePath->path_len ==> \mutable(writeSet[j]))
	_(invariant \forall unsigned i; i<pathlist->resource->num_paths ==> pathlist->resource->pathlist[i] != onePath)
	_(invariant \forall unsigned j; j<onePath->path_len ==>  writeSet[j] == grid->gridPoints[onePath->xs[j]]->resource)
	_(invariant \forall unsigned k;{pathlist->resource->pathlist[k]} k<pathlist->resource->num_paths ==> \forall unsigned i,j; i<pathlist->resource->pathlist[k]->path_len && j<onePath->path_len ==> pathlist->resource->pathlist[k]->xs[i] != onePath->xs[j])
	//_(invariant \mutable(pathlist->resource))
	_(invariant \forall unsigned j; j< i ==> grid->gridPoints[onePath->xs[j]]->resource->data == (int) onePath->ID)
	_(invariant \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==>  \forall unsigned i; i<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[i]]->resource->data == (int) pathlist->resource->pathlist[j]->ID)
	_(invariant \forall unsigned i; {writeSet[i]} i<onePath->path_len ==> \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==> \forall unsigned k; k<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[k]]->resource != writeSet[i])
	_(invariant \wrapped(pathlist->resource))
	_(writes \array_range(writeSet, onePath->path_len))
	{
		_(assume \writable(writeSet[i]))
		writeSet[i]->data = (int) onePath->ID;
	}

	_(assert \forall unsigned k;{pathlist->resource->pathlist[k]} k<pathlist->resource->num_paths ==> \forall unsigned i,j; i<pathlist->resource->pathlist[k]->path_len && j<onePath->path_len ==> pathlist->resource->pathlist[k]->xs[i] != onePath->xs[j])
	_(assert \forall unsigned i; i<onePath->path_len ==> grid->gridPoints[onePath->xs[i]]->resource->data == (int) onePath->ID)
	_(assert \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==>  \forall unsigned i; i<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[i]]->resource->data == (int) pathlist->resource->pathlist[j]->ID)

	_(unwrap pathlist->resource)
	_(assume pathlist->resource->num_paths< MAX_PATHS-1)

	pathlist->resource->pathlist[pathlist->resource->num_paths] = onePath;
	pathlist->resource->num_paths++;

	_(assert \forall unsigned i; i<onePath->path_len ==> grid->gridPoints[onePath->xs[i]]->resource->data == (int) onePath->ID)
	_(assert \forall unsigned j;{pathlist->resource->pathlist[j]} j<pathlist->resource->num_paths ==>  \forall unsigned i; i<pathlist->resource->pathlist[j]->path_len ==> grid->gridPoints[pathlist->resource->pathlist[j]->xs[i]]->resource->data == (int) pathlist->resource->pathlist[j]->ID)

	_(wrap pathlist->resource)
	for(i=0;i<onePath->path_len; i++)
	_(invariant \forall unsigned j; j<i ==> \wrapped(writeSet[j]))
	_(invariant \forall unsigned j; j>=i && j<onePath->path_len ==> \mutable(writeSet[j]))
	_(writes \array_range(writeSet,onePath->path_len))
	{
		_(wrap writeSet[i])
	}
	//_(assert \false)
}