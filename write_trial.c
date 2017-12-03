#include<vcc.h>
#include <limits.h>


typedef struct SpanFormer SpanFormer, *PSpanFormer;
typedef struct IntHandle IntHandle, *PIntHandle;
typedef struct Int Int, *PInt;
typedef struct TM TM, *PTM;
typedef struct Trans Trans, *PTrans;

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
  //_(ghost \object protected_obj)
  _(invariant \mine(&claim_counter))
  _(invariant (&claim_counter)->\claim_count == cnt >> 1)
  _(invariant \on_unwrap(\this, \false))

  //_(invariant protected_obj != &claim_counter)
  //_(invariant protected_obj != &token)
  _(invariant (cnt & 1) == 0 ==> \mine(&token))
  _(invariant (cnt != 1) ==> \mine(protected_obj))
  _(invariant \mine(&token) || \mine(protected_obj))

  _(ghost struct LockProtector* protected_obj)
};


_(ghost struct Int{
	int data;
	int vNo;
};)

_(claimable)  struct IntHandle {
	
	 PSpanFormer integerLock;
	_(ghost  PTM tm)   // TM managing this field
	_(ghost struct LockProtector* po)

	_(invariant tm->mng[\this] && tm->\closed)

	_(invariant \mine(integerLock))
	_(invariant integerLock->\closed)
	_(invariant integerLock->cnt != 1 ==> tm->memInt[\this] == \old(tm->memInt[\this])) //If lock is not taken, nobody can change TM map
	_(invariant \old(tm->memInt[\this]) != tm->memInt[\this] ==> tm->memInt[\this] \in integerLock->protected_obj->\owns) //If Lock is taken, only the owner trans can modify

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

} TM;

struct Trans{	//Represents transaction related data, it can be opened
	int dummy;
	_(ghost PInt writeSet[PIntHandle])
	_(ghost \bool readSet[PIntHandle])
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

void obtain_int(PIntHandle p _(ghost \claim c) _(out PInt o))
_(always c, p->\closed)
_(ensures o != p->tm->memInt[p] && ((PInt)o)->data == p->tm->memInt[p]->data && ((PInt)o)->vNo == p->tm->memInt[p]->vNo && \wrapped(o) &&\mutable(o))
;

void foo(PIntHandle p, _(ghost PInt data) _(ghost \claim c) _(ghost PTM tm) _(ghost PTrans trans))
_(always c, p->\closed && tm->\closed && (\forall PIntHandle x; tm->mng[x] ==> tm->memInt[x]->\closed))
_(requires tm == p->tm)
_(requires \wrapped(data) && \wrapped(trans))
_(requires \forall PIntHandle x; !trans->writeSet[x])
_(writes data, trans)
{
	begin_write_span(p->integerLock, _(ghost c));
	//obtain_int(p, _(ghost c) _(out data));
	//_(assert p->integerLock->cnt == 1)
	_(unwrap data)
		_(atomic p, p->tm, p->tm->memInt[p],c){
			_(ghost data->data = p->tm->memInt[p]->data)
			_(ghost data->vNo = p->tm->memInt[p]->vNo)
		}
		_(ghost data->data = 4)
		_(ghost _(unchecked) data->vNo++)
	_(wrap data)
	_(unwrap trans)
		_(ghost trans->writeSet = \lambda PIntHandle x; (x==p) ? data : trans->writeSet[x])
	_(wrap trans)

	_(unwrap p->integerLock->protected_obj)
	_(ghost  p->integerLock->protected_obj->\owns += data)
	_(wrap p->integerLock->protected_obj)

	_(atomic tm,c){
		_(ghost tm->memInt = \lambda PIntHandle x; trans->writeSet[x] ? trans->writeSet[x]:  \old(tm->memInt[x]))

		}
		
	_(assert \false)

}
