#include<vcc.h>
#include <limits.h>
#include<stdlib.h>


typedef struct SpanFormer SpanFormer, *PSpanFormer;
typedef struct IntHandle IntHandle, *PIntHandle;
typedef struct Int Int, *PInt;
typedef struct TM TM, *PTM;
typedef struct Trans Trans, *PTrans;
typedef struct S S, *PS;
typedef struct SHandle SHandle, *PSHandle;

/*Compiler supported atomic functions*/
_(atomic_inline) unsigned InterlockedCompareExchange(volatile unsigned *Destination, unsigned Exchange, unsigned Comparand) {
  if (*Destination == Comparand) {
    *Destination = Exchange;
    return Comparand;
  } else {
    return *Destination;
  }
}

 _(dynamic_owns) struct LockProtector{
	int dummy;
};

/* Structs */
_(ghost struct Token {
  int dummy;
})
_(ghost _(claimable) struct Counter {
  int dummy;
})
/*{refcnt}*/
_(volatile_owns) struct SpanFormer {
  volatile unsigned cnt;
  _(ghost struct Token token)
  _(ghost struct Counter claim_counter)
  _(ghost struct LockProtector* protected_obj)

  _(invariant \mine(&claim_counter))
  _(invariant (&claim_counter)->\claim_count == cnt >> 1)
  _(invariant \on_unwrap(\this, \false))

  _(invariant (cnt & 1) == 0 ==> \mine(&token))
  _(invariant (cnt != 1) ==> \mine(protected_obj))
  _(invariant \mine(&token) || \mine(protected_obj))
};

_(ghost struct Int{
	int data;
	int vNo;
};)

_(claimable)  struct IntHandle {
	
	 PSpanFormer integerLock;
	_(ghost  PTM tm)   // TM managing this field

	_(invariant tm->mng[\this] && tm->\closed)

	_(invariant \mine(integerLock))
	_(invariant integerLock->\closed)
	_(invariant integerLock->cnt != 1 ==> tm->memInt[\this] == \old(tm->memInt[\this])) //If lock is not taken, nobody can change TM map
	_(invariant \old(tm->memInt[\this]) != tm->memInt[\this] ==> tm->memInt[\this] \in integerLock->protected_obj->\owns) //If Lock is taken, only the owner trans can modify

	_(invariant \on_unwrap(\this,\false)) // This object is always closed.
};

_(ghost struct S{
	PInt x;
	PInt y;
	int vNo;

	_(invariant \mine(x) && \mine(y))
	_(invariant x->data == y->data)
	_(invariant x->vNo == y->vNo)
};)



struct SHandle{
	PSpanFormer lock;
	_(ghost PTM tm)

	_(invariant tm->mngS[\this] && tm->\closed)
	_(invariant \mine(lock))
	_(invariant lock->\closed)

	_(invariant lock->cnt != 1 ==> tm->memS[\this] == \old(tm->memS[\this])) //If lock is not taken, nobody can change TM map
	_(invariant \old(tm->memS[\this]) != tm->memS[\this] ==> tm->memS[\this] \in lock->protected_obj->\owns) //If Lock is taken, only the owner trans can modify

	_(invariant \on_unwrap(\this,\false)) // This object is always closed.

};


typedef _(volatile_owns) _(claimable) struct TM{
	int dummy;
	//_(ghost volatile \bool mng[PInt])
	//_(ghost volatile PInt memInt[PIntHandle])
	_(ghost volatile PInt memInt[PIntHandle])
	_(ghost volatile \bool mng[PIntHandle])

	_(invariant \unchanged(mng) || (\forall PIntHandle p; \old(mng[p])==> \inv2(p) ))
	_(invariant \forall PIntHandle p; \old(mng[p]) ==> mng[p])
	_(invariant \forall PIntHandle p; mng[p] ==> p->tm == \this && p->\closed )
	_(invariant \forall PIntHandle x; \old(memInt[x]) ==> \unchanged(memInt[x]) || \inv2(x))

	_(invariant \forall PIntHandle p; mng[p] ==> memInt[p])

	//_(invariant \forall PInt p; p->\closed ==> \mine(p)) // does not work
	//_(invariant \forall PTM p,q; p!= 0 && q!= 0 ==> p == q) //does not work
	_(invariant \on_unwrap(\this,\false))

	_(ghost volatile \bool mngS[PSHandle])
	_(invariant \unchanged(mngS) || (\forall PSHandle p; \old(mngS[p])==> \inv2(p) ))
	_(ghost volatile PS memS[PSHandle])
	_(invariant \forall PSHandle p; \old(mngS[p]) ==> mngS[p])
	_(invariant \forall PSHandle p; mngS[p] ==> p->tm == \this && p->\closed )
	_(invariant \forall PSHandle x; \old(memS[x]) ==> \unchanged(memS[x]) || \inv2(x))

	_(invariant \forall PSHandle p; mngS[p] ==> memS[p])

} TM;

struct Trans{	//Represents transaction related data, it can be opened
	int dummy;
	_(ghost PInt writeSet[PIntHandle])
	_(ghost \bool readSet[PIntHandle])

	_(ghost PS writeSetS[PSHandle])
	_(ghost \bool readSetS[PSHandle])
};

/*SpanFormer methods */
void begin_read_span( PSpanFormer r _(ghost \claim c)
             _(out \claim ret))
  _(always c, r->\closed)
  _(ensures \claims_object(ret, &r->claim_counter) && \claims(ret, r->protected_obj->\closed) && \wrapped0(ret) && \fresh(ret))
;

void end_read_span(PSpanFormer r _(ghost \claim c) _(ghost \claim handle))
  _(always c, r->\closed)
  _(requires \claims_object(handle, &r->claim_counter) && \wrapped0(handle))
  _(requires c != handle)
  _(writes handle)
  ;

void update_to_write_span(PSpanFormer r _(ghost \claim c) _(ghost \claim handle))
_(always c, r->\closed)
_(requires \claims_object(handle, &r->claim_counter) && \wrapped0(handle))
_(requires c != handle)
_(ensures \wrapped(r->protected_obj) && \fresh(r->protected_obj))
;

void begin_write_span(PSpanFormer r _(ghost \claim c))
  _(always c, r->\closed)
  _(ensures \wrapped(r->protected_obj) && \fresh(r->protected_obj) && r->cnt == 1)
;
void end_write_span(PSpanFormer r _(ghost \claim c))
  _(always c, r->\closed)
  //_(requires c != r->protected_obj)
  _(requires \wrapped(r->protected_obj))
  _(writes r->protected_obj)
  ;

/*void write_to_int(PIntHandle p _(ghost \claim c) _(ghost PInt data) _(ghost PTrans trans))
_(always c, p->\closed && p->tm->\closed && (\forall PIntHandle x; p->tm->mng[x] ==> p->tm->memInt[x]->\closed))
_(requires \wrapped(p->integerLock->protected_obj) && p->integerLock->cnt != 1 && \wrapped(data))
_(writes data, trans);*/

/* original foo2:
void foo(struct s)
{
  _(begin_trans)
   write_trans( s->x, 8);
   write_trans(s->y, 8);
  _(commit_trans)
  _(assert s->x == 8 && s-> y == 8)
  _(end_trans)
}

An intermediate translation would be:
void foo(struct s)
{
	struct s temp_s;
	_(begin_trans)
	temp_s = relaxed_read(s);
	temp_s->x = 8;
	temp_s->y = 8;
	_(commit_trans)
	_(assert s->x == 8 && s-> y == 8)
	_(end_trans)
}*/

void foo2(PSHandle s, _(ghost \claim c) _(ghost PTM tm))
_(always c, s->\closed && tm->\closed && (\forall PIntHandle x; tm->mng[x] ==> tm->memInt[x]->\closed) && (\forall PSHandle x; tm->mngS[x] ==> tm->memS[x]->\closed) )
_(requires s->tm == tm)
{
	/*create temp_s */
	_(ghost PS temp_s = malloc(sizeof(S)))
	_(assume temp_s)
	_(ghost temp_s->x = malloc(sizeof(Int)))
	_(assume temp_s->x)
	_(ghost temp_s->y = malloc(sizeof(Int)))
	_(assume temp_s->y)
	/*create temp_s */

	/* begin trans */
	PTrans trans = malloc(sizeof(Trans));
	_(assume trans)
	_(ghost  trans->writeSetS = \lambda PSHandle x; ((PS)0))
	_(ghost  trans->writeSet = \lambda PIntHandle x; ((PInt)0))
	_(ghost trans->readSet = \lambda PIntHandle x; \false)
	_(ghost trans->readSetS = \lambda PSHandle x; \false)
	/* begin trans */

	/* temp_s = relaxed_read(s); */
	_(atomic c, s,s->tm, s->tm->memS[s])
	{
		_(ghost temp_s->x->data = s->tm->memS[s]->x->data)
		_(ghost temp_s->x->vNo = s->tm->memS[s]->x->vNo)
		_(ghost temp_s->y->data = s->tm->memS[s]->y->data)
		_(ghost temp_s->y->vNo = s->tm->memS[s]->y->vNo)
	}
	/* temp_s = relaxed_read(s); */

	/* temp_s->x = 8; */
	begin_write_span(s->lock, _(ghost c));		//since we wrote to s first time
	_(ghost trans->writeSetS = \lambda PSHandle x; x==s ? temp_s : trans->writeSetS[x]) //since we wrote to s first time

	_(ghost temp_s->x->data = 8)
	_(ghost  _(unchecked) temp_s->x->vNo ++)
	/* temp_s->x = 8; */

	/* temp_s->y = 8; */
	_(ghost temp_s->y->data = 8)
	_(ghost  _(unchecked) temp_s->y->vNo ++)
	/* temp_s->y = 8; */

	/* _(commit_trans) */
	//First close the temp objects you want to write to
	_(wrap temp_s->x)
	_(wrap temp_s->y)

	_(wrap temp_s)
	
	//Add these objects to owns set of the object handle so that you can commit
	_(unwrap s->lock->protected_obj)
	_(ghost  s->lock->protected_obj->\owns += temp_s)
	_(wrap s->lock->protected_obj)

	//Update maps
	_(atomic tm,c){
		_(ghost tm->memInt = \lambda PIntHandle x; trans->writeSet[x] ? trans->writeSet[x]:  \old(tm->memInt[x]))
		_(ghost tm->memS = \lambda PSHandle x; trans->writeSetS[x] ? trans->writeSetS[x]:  \old(tm->memS[x]))
		}
	/* _(commit_trans) */

	_(assert tm->memS[s]->x->data == 8  && tm->memS[s]->y->data == 8)
	/* _(end_trans) */
	free(trans);
	end_write_span(s->lock _(ghost c));
	/* _(end_trans) */

	//_(assert \false)
}