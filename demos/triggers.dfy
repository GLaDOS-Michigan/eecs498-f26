predicate P(x:int)
predicate Q(x:int)

lemma foo()
    requires forall x {:trigger P(x)}:: P(x) && Q(x)
    ensures Q(0)
{
    
}
