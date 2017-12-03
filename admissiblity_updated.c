#include<vcc.h>
#include<stdlib.h>
#include<limits.h>

typedef struct A A, *PA;
typedef struct B B, *PB;
typedef struct AHandle AHandle, *PAHandle;
typedef struct BHandle BHandle, *PBHandle;
typedef struct TM TM, *PTM;
typedef struct Trans Trans, *PTrans;
typedef struct Node Node, *PNode;
typedef struct Int Int, *PInt;
typedef struct Lock Lock, *PLock;
typedef struct SpinLock SpinLock, *PSpinLock;

_(atomic_inline) unsigned InterlockedCompareExchange(volatile unsigned *Destination, unsigned Exchange, unsigned Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}

_(volatile_owns) struct A1{
	_(ghost \object po)
	struct A2* a2;

	_(invariant \mine(a2))
	_(invariant a2->a1 == \this)
	_(invariant \unchanged(\this->\owns) || \inv2(a2))
	_(invariant \mine(po) || po \in a2->\owns)
};

_(volatile_owns) struct A2{
	_(ghost \object po)
	struct A1* a1;

	_(invariant a1->\closed ==>(\unchanged(\this->\owns) || \inv2(a1)))
	//_(invariant a1->
	//_(invariant \unchanged(\this->\owns) || \inv2(a1))
};

_(claimable) struct Token{
	int a;
};
_(claimable) struct Token2{
	int a;
};

_(claimable) struct Token3{
	int a;
};

_(volatile_owns) struct Lock{
	volatile unsigned rCnt;
	volatile unsigned wCnt;
	_(ghost struct Token1* rClaim)
	_(ghost struct Token2* wClaim)
	PA po;

	_(invariant \mine(rClaim) && \mine(wClaim))
	_(invariant (rCnt >> 1) == rClaim->\claim_count)
	_(invariant (wCnt >> 1) == wClaim->\claim_count)

	_(invariant  wCnt <= 2)
	_(invariant ((rCnt>>1) >0 ) ==> wCnt == 0 )
	_(invariant wCnt != 1 ==> \mine(po) )

	_(invariant \on_unwrap(\this,\false))
};

_(claimable) struct A{
	int a;
	_(ghost PB lock)
	
	//_(invariant \forall PB  b; b->\closed  && b->po ==\this==> \inv2(b))
};

_(volatile_owns) struct SpinLock{
	volatile unsigned locked;
	PTM tm;
	_(invariant locked == 0 ==> \mine(tm))
	_(invariant \on_unwrap(\this,\false))
};

_(volatile_owns) struct LittleLock{
	volatile unsigned cnt;
	_(ghost struct Token2 token)
	PA po;
	_(ghost struct BigLock* bl)

	_(invariant \mine(&token))
	_(invariant cnt == (&token)->\claim_count)
	_(invariant cnt <= 1)
	_(invariant cnt == 1 <==> \mine(po))
	_(invariant \on_unwrap(\this,cnt==0))

	//_(invariant \forall struct BigLock *p; p->\closed && p->ll == \this ==> \inv2(p))
	_(invariant \unchanged(\this->\owns) || \inv2(bl) )
};

_(volatile_owns) struct BigLock{
	volatile unsigned cnt;
	_(ghost struct Token token)
	_(ghost struct Token3 xch)
	PA po;
	_(ghost struct LittleLock *ll)

	_(invariant \mine(&token) &&\mine(ll))
	_(invariant cnt>>1 == (&token)->\claim_count)
	_(invariant cnt != 1 ==> \mine(po))
	_(invariant \on_unwrap(\this, cnt>>1 == 0))

	_(invariant ll->bl == \this)
	_(invariant \unchanged(\this->\owns) || \inv2(ll) )
	_(invariant \mine(po) || po \in ll->\owns)

	_(invariant (cnt &1) == 0 ==> \mine(&xch))
	_(invariant \mine(&xch) || \mine(po))

};

_(dynamic_owns) struct TM{

	int a;
	_(ghost \bool mng[struct BigLock*])
	_(invariant \forall struct BigLock *p; mng[p] ==>\mine(p))
};


struct Next{
	int a;
	struct BigLock* next;
	_(invariant \mine(next))
	_(invariant next->po->a <a)
};

_(volatile_owns) struct B{
	int a;
	_(ghost PA po)
	volatile unsigned cnt;

	//_(invariant po->\closed ==> po->lock == \this)
	//_(invariant cnt == po->\claim_count)

	_(invariant \mine(po))
	_(invariant po->\claim_count == cnt>>1)
	_(invariant cnt<8)
	_(invariant \on_unwrap(\this,\false))
};

void foo(PTM tm, struct BigLock* a _(ghost \claim c))
_(always c, tm->\closed && (tm->\closed ==> a \in tm->\owns) && (tm->\closed && a->cnt != 1 ==> a->po \in a->\owns))
_(requires tm->mng[a] && a->cnt == 3 && a->po)
{
	int x;
	_(ghost \claim cread)

	//relaxed read
	_(atomic _(read_only)a, _(read_only)a->po, c){

		x = a->po->a;
	}


	unsigned v,n;
	//read
	for(;;)
	{
		_(atomic c,a){ v=a->cnt;}
		if(v &1) continue;
		_(assume v <= UINT_MAX - 2)
		_(atomic c,a){
			n= InterlockedCompareExchange(&a->cnt,v+2,v);
			_(ghost
			if (v == n) cread = \make_claim({&a->token}, a->\closed && a->cnt >> 1 > 0 && a->po->\closed))
		}
		if(v==n) break;
	}


	//write
	
	//_(assert \false)
}

void acquireTMLock(PSpinLock tm_lock, PTM tm, struct BigLock* a _(ghost \claim c) )
_(always c, tm_lock->\closed && (tm_lock->\closed && tm_lock->locked == 0 ==> tm \in tm_lock->\owns)  && (!tm_lock->locked  ==> tm->mng[a] && a \in tm->\owns && a->ll \in a->\owns)
	&& (!tm_lock->locked && a->cnt != 1 ==> a->po \in a->\owns) && (!tm_lock->locked && a->cnt == 1 ==> a->po \in a->ll->\owns))
_(requires tm_lock->tm == tm && tm->mng[a] )
_(ensures \wrapped(tm_lock->tm) && \fresh(tm_lock->tm))
{
	unsigned z,x;
	z=0;
	for(;;){
	_(atomic c,tm_lock){
		x = InterlockedCompareExchange(&tm_lock->locked,1,0);
		if(x ==0)
		{
			_(ghost tm_lock->\owns -= tm_lock->tm)
			//_(assert \false)
			z = 1;
		}
	}
	if( z!= 0) break;
	
	}
}

void relaxedRead(PSpinLock tm_lock, PTM tm, struct BigLock* a _(ghost \claim c) )
_(always c, tm_lock->\closed && (tm_lock->\closed && tm_lock->locked == 0 ==> tm \in tm_lock->\owns)  && (!tm_lock->locked  ==> tm->mng[a] && a \in tm->\owns && a->ll \in a->\owns)
	&& (!tm_lock->locked && a->cnt != 1 ==> a->po \in a->\owns) && (!tm_lock->locked && a->cnt == 1 ==> a->po \in a->ll->\owns))
_(requires tm_lock->tm == tm && tm->mng[a] )
_(writes a)
{
	unsigned y,x;
	int z=0;
	_(ghost int zz)
	PTM bl;
	struct BigLock* bbl;
	_(ghost \claim cx)
	PA pa;

	//Relaxed Read
	for(;;){
	_(atomic c,tm_lock){
		x = InterlockedCompareExchange(&tm_lock->locked,1,0);
		if(x ==0)
		{
			_(ghost tm_lock->\owns -= tm)
			//_(assert \false)
			z = 1;
		}
	}
	if( z!= 0) break;
	
	}

	_(assert \wrapped(tm) && a \in tm->\owns && tm->mng[a] && a->ll \in a->\owns )
	_(assert a->cnt != 1 ==> a->po \in a->\owns && a->cnt == 1 ==> a->po \in a->ll->\owns)

	_(atomic a,a->po){
		_(assert a->\closed)
		x = a->cnt;
		z = a->po->a;
		//_(assert \false)
	}


	_(atomic tm_lock,c){
		tm_lock->locked = 0;
		_(ghost tm_lock->\owns += tm)
	}

	//_(assert \false)
}

void read(PSpinLock tm_lock, PTM tm, struct BigLock* a _(ghost \claim c) )
_(always c, tm_lock->\closed && (tm_lock->\closed && tm_lock->locked == 0 ==> tm \in tm_lock->\owns)  && (!tm_lock->locked  ==> tm->mng[a] && a \in tm->\owns && a->ll \in a->\owns)
	&& (!tm_lock->locked && a->cnt != 1 ==> a->po \in a->\owns) && (!tm_lock->locked && a->cnt == 1 ==> a->po \in a->ll->\owns))
_(requires tm_lock->tm == tm && tm->mng[a] )
{
	unsigned y,x;
	int z=0;
	_(ghost int zz)
	PTM bl;
	struct BigLock* bbl;
	_(ghost \claim cx)
	PA pa;
	//Read
	for(;;)
	{
	z=0;
	for(;;)
	{
	_(atomic c,tm_lock){
		x = InterlockedCompareExchange(&tm_lock->locked,1,0);
		if(x ==0)
		{
			_(ghost tm_lock->\owns -= tm)
			//_(assert \false)
			z = 1;
		}
	}
	if( z!= 0) break;
	
	}

	_(assert \wrapped(tm) && a \in tm->\owns && tm->mng[a] && a->ll \in a->\owns )
	_(assert a->cnt != 1 ==> a->po \in a->\owns && a->cnt == 1 ==> a->po \in a->ll->\owns)

	_(atomic c,a,a->po){ x = a->cnt ;}
	if(x & 1) continue;

	_(assume x < 1000)
	_(atomic c,a){
		y = InterlockedCompareExchange(&a->cnt, x+2, x);
		_(ghost if(x== y) cx = \make_claim({&a->token},a->po->\closed && a->\closed && a->cnt >> 1 > 0 ))
	}
	if(x==y) break;

	_(atomic tm_lock,c){
		tm_lock->locked = 0;
		_(ghost tm_lock->\owns += tm)
	}
	//_(assert \false)
	}
	_(assert \wrapped(cx) && \claims(cx, a->po->\closed))
		int t;
	_(atomic cx, a->po){
		t = a->po->a;
	}
	//_(assert \false)
}

void write(PSpinLock tm_lock, PTM tm, struct BigLock* a _(ghost \claim c) )
_(always c, tm_lock->\closed && (tm_lock->\closed && tm_lock->locked == 0 ==> tm \in tm_lock->\owns)  && (!tm_lock->locked  ==> tm->mng[a] && a \in tm->\owns && a->ll \in a->\owns)
	&& (!tm_lock->locked && a->cnt != 1 ==> a->po \in a->\owns) && (!tm_lock->locked && a->cnt == 1 ==> a->po \in a->ll->\owns))
_(requires tm_lock->tm == tm && tm->mng[a] )
{
	unsigned y,x;
	int z=0;
	_(ghost int zz)
	PTM bl;
	struct BigLock* bbl;
	_(ghost \claim cx)
	PA pa;
	//Read
	for(;;)
	{
	z=0;
	for(;;)
	{
	_(atomic c,tm_lock){
		x = InterlockedCompareExchange(&tm_lock->locked,1,0);
		if(x ==0)
		{
			_(ghost tm_lock->\owns -= tm)
			//_(assert \false)
			z = 1;
		}
	}
	if( z!= 0) break;
	
	}

	_(assert \wrapped(tm) && a \in tm->\owns && tm->mng[a] && a->ll \in a->\owns )
	_(assert a->cnt != 1 ==> a->po \in a->\owns && a->cnt == 1 ==> a->po \in a->ll->\owns)

	_(atomic c,a,a->po){ x = a->cnt ;}
	if((x & 1)) continue;

	_(atomic c,a,a->ll){
		y = InterlockedCompareExchange(&a->cnt, x|1, x);
		_(ghost if( y==x){ 
			a->ll->cnt = 0;
		})
		
	}

	if(x==y) break;

	_(atomic tm_lock,c){
		tm_lock->locked = 0;
		_(ghost tm_lock->\owns += tm)
	}
	//_(assert \false)
	}
	//_(assert \false)
}

/*struct AHandle{
	int a;
	_(ghost \object lock)
	_(ghost PTM tm)
};

struct BHandle{
	int a;
	_(ghost \object lock)
	_(ghost PTM tm)
};

struct A{

	int a;
};

struct B{
	PA a;
	int b;
};

void havoc(_(ghost \object obj))
_(writes obj)
;

struct Trans{
	int a;
	_(ghost int writeAa[PAHandle])
	_(ghost int writeBb[PBHandle])
	_(ghost PA writeBa[PBHandle])
};

_(dynamic_owns) struct TM{
	int a;
	_(ghost volatile PA memA[PAHandle])
	_(ghost volatile PB memB[PBHandle])

	_(invariant \forall PBHandle b; memB[b] ==> \mine(memB[b]))
	_(invariant \forall PAHandle b; memA[b] ==> \mine(memA[b]))
	_(invariant \on_unwrap(\this, \false))
	_(invariant \forall PBHandle b; memB[b]->a->a < a)
};

void foo(PAHandle a, PBHandle b _(ghost PTM tm))
{
	//TM in içindeki mapteki objeler ile trans maplerindeki objeleri ayrý yapmak istersek hepsini kendileri own etsin?
	PA a_local = malloc(sizeof(A));
	_(assume a)
	PB b_local = malloc(sizeof(A)); 
	_(assume b)
	PTrans trans = malloc(sizeof(Trans));
	_(assume trans)
	a_local->a = 5;
	trans->writeSetAa[a] = 5;
	b_local->a = tm->memA[a];
	trans->writeSetBa[b] = tm->memA[a];

	_(ghost PA memAtemp[PAHandle])
	_(ghost PB memBtemp[PBHandle])

	havoc(memAtemp);
	havoc(memBtemp);

	_(atomic tm){
		_(assume \forall PAHandle pa; memAtemp[pa] == tm->memA[pa] &&  (trans->writeSetAa[pa] ==> memAtemp[pa]->a == trans->writeSetAa[pa]))
		_(tm->memA = memAtemp)
	}

	_(assert \false)
}*/