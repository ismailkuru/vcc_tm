//TODO: PathListLock için write fonk. yaz. Sonra gridi yap.

#include<vcc.h>
#include<stdlib.h>
#include<limits.h>

#define WIDTH 10
#define HEIGHT 10
#define DEPTH 10
#define MAX_POINTS 30
#define MAX_PATHS 20

#define GRID_POINT_EMPTY  -1
#define GRID_POINT_FULL -2
#define OWNER_NULL -1

typedef struct Token Token, *PToken;
typedef struct GridLock GridLock, *PGridLock;
typedef struct Grid Grid, *PGrid;
typedef struct Path Path, *PPath;
typedef struct PathList PathList, *PPathList;

_(atomic_inline) unsigned InterlockedCompareExchange(volatile unsigned *Destination, unsigned Exchange, unsigned Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}


struct Grid{
	int gridPoints[WIDTH][HEIGHT][DEPTH];
};

struct Path{
	
	int xs[MAX_POINTS];
	int ys[MAX_POINTS];
	int zs[MAX_POINTS];

	int lastx_point;
	int lasty_point;
	int lastz_point;
	
	int ID;
	
	int path_len;
	_(invariant \mine(xs) && \mine(ys) && \mine(zs))
};

struct PathList{
	
	Path pathlist[MAX_PATHS];
	int num_paths; // num_paths < MAX_PATHS of pathlist contain a path
	_(invariant \mine(pathlist))			  
};

_(ghost struct Token {
  int dummy;
})

_(ghost struct Token2 {
  int dummy;
})

_(ghost _(claimable) struct Counter {
  int dummy;
})

void read(PGridLock r _(ghost \claim c)
             _(out \claim ret))
  _(always c, r->\closed)
  _(ensures \claims_object(ret, &r->claim_counter) && \claims(ret, r->po->\closed && r->cnt >> 1 > 0 && r->po->\closed && r->cmt != 1) && \wrapped0(ret) && \fresh(ret))
{
  unsigned v, n;

  for (;;) {
    _(atomic c, r) { v = r->cnt; }
    if (v & 1) continue;
	
    _(assume v <= UINT_MAX - 2)
    _(atomic c, r) {
      n = InterlockedCompareExchange(&r->cnt, v + 2, v);
      _(ghost
        if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0 && r->po->\closed && r->cmt != 1))
       // if (v == n) ret = \make_claim({&r->claim_counter}, r->\closed && r->cnt >> 1 > 0))
    }
    if (v == n) return;
  }
}

_(volatile_owns) struct GridLock {
  volatile unsigned cnt;
  PGrid po;
  _(invariant \mine(&claim_counter))
  _(invariant (&claim_counter)->\claim_count == cnt >> 1)
  _(invariant \on_unwrap(\this, (&claim_counter)->\claim_count == 0))

  _(ghost struct Token token)
  _(ghost struct Token2 token2)
  _(ghost struct Counter claim_counter)
  _(invariant (cnt & 1) == 0 ==> \mine(&token))
  _(invariant (cnt != 1) ==> (\mine(po) && \mine(&token2)))
  _(invariant \mine(&token) || \mine(po))
  _(invariant \mine(&token) || \mine(&token2))
  _(invariant \mine(&token2) || \mine(po))

  volatile unsigned cmt;
  _(invariant cmt ==0 || cmt ==1)
  _(invariant cnt != 1 ==> cmt==0)
  _(invariant cnt == 1 && cmt == 1 ==> \mine(&token2) && !\mine(po))
  _(invariant cnt == 1 && cmt == 0 ==> \mine(po))

  volatile int rd_cp[WIDTH][HEIGHT][DEPTH];
  _(invariant \mine(rd_cp))
  _(invariant cmt != 1 ==> (\forall unsigned i,j,k; i<WIDTH  && j<HEIGHT && k<DEPTH ==>rd_cp[i][j][k] == po->gridPoints[i][j][k]))
};

_(volatile_owns) struct PathListLock {
  volatile unsigned cnt;
  PPathList po;
  _(invariant \mine(&claim_counter))
  _(invariant (&claim_counter)->\claim_count == cnt >> 1)
  _(invariant \on_unwrap(\this, (&claim_counter)->\claim_count == 0))

  _(ghost struct Token token)
  _(ghost struct Token2 token2)
  _(ghost struct Counter claim_counter)
  _(invariant (cnt & 1) == 0 ==> \mine(&token))
  _(invariant (cnt != 1) ==> (\mine(po) && \mine(&token2)))
  _(invariant \mine(&token) || \mine(po))
  _(invariant \mine(&token) || \mine(&token2))
  _(invariant \mine(&token2) || \mine(po))

  volatile unsigned cmt;
  _(invariant cmt ==0 || cmt ==1)
  _(invariant cnt != 1 ==> cmt==0)
  _(invariant cnt == 1 && cmt == 1 ==> \mine(&token2) && !\mine(po))
  _(invariant cnt == 1 && cmt == 0 ==> \mine(po))

  volatile Path pathlist[MAX_PATHS];
  volatile int num_paths;
  _(invariant \mine(pathlist))
  _(invariant cmt != 1 ==> (\forall unsigned i;{pathlist[i]} i<MAX_PATHS ==>
		(\forall unsigned j;{po->pathlist[i].xs[j]}  j<MAX_POINTS ==> 
				pathlist[i].xs[j] == po->pathlist[i].xs[j] && pathlist[i].ys[j] == po->pathlist[i].ys[j] && pathlist[i].zs[j] == po->pathlist[i].zs[j] )
				&& po->pathlist[i].ID == pathlist[i].ID && po->pathlist[i].path_len == pathlist[i].path_len && po->pathlist[i].lastx_point == pathlist[i].lastx_point
				&& po->pathlist[i].lasty_point == pathlist[i].lasty_point && po->pathlist[i].lastz_point == pathlist[i].lastz_point))
	_(invariant cmt !=1 ==> num_paths == po->num_paths)

};

PGrid read_grid(PGridLock grid _(ghost \claim c) _(ghost \claim cx))
_(always c, grid->\closed)
_(requires \claims_object(cx, &grid->claim_counter))
_(always cx,  grid->po->\closed && grid->cnt >> 1 > 0 && grid->po->\closed && grid->cmt != 1)
_(ensures \forall unsigned i,j,k; i<WIDTH && j<HEIGHT && k<DEPTH ==> (\result)->gridPoints[i][j][k] == grid->po->gridPoints[i][j][k])
;
/*{
	PGrid localGrid = (PGrid) malloc(sizeof(Grid));
	PGrid temp;
	_(assume localGrid)
	unsigned i,j,k;
	//_(ghost \claim cx)
	//read(grid _(ghost c) _(out cx));

	for(i=0; i<WIDTH; i++)
	_(invariant \active_claim(cx))
	_(invariant \wrapped(cx))
	_(invariant \writable(localGrid))
	{
		for(j=0; j<HEIGHT; j++)
		_(invariant \active_claim(cx))
		_(invariant \wrapped(cx))
		_(invariant \writable(localGrid))
		{
			for(k=0; k<DEPTH; k++)
			_(invariant \wrapped(cx) && \active_claim(cx) && \wrapped(c) && \active_claim(c))
			_(invariant \writable(localGrid))
			_(invariant grid->po->\closed && grid->\closed && grid->cmt != 1)
			//_(invariant \forall unsigned x; x<k ==> \unchanged(grid->po->gridPoints[0][0][x]))
			//_(invariant \forall unsigned x; x<k ==> localGrid->gridPoints[0][0][x] == grid->po->gridPoints[0][0][x])
			{
				_(assert grid->cmt != 1)
				_(atomic c,_(read_only)grid){temp = grid->po;}
				_(assert \claims_object(cx,&grid->claim_counter))
				_(atomic cx,  _(read_only)temp){ localGrid->gridPoints[0][0][k] = temp->gridPoints[0][0][k];}

			}}}
	return localGrid;
	//_(assert \false)
}*/