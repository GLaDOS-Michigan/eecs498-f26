// Height is in mm
type Height = int

predicate IsTall(h: Height)

lemma BaseCase()
  ensures IsTall(2000)

lemma SoritesStep(h: Height)
  requires IsTall(h)
  ensures IsTall(h - 1)

lemma SoritesParadox()
  ensures IsTall(1000)
{
  BaseCase();

  var currentHeight := 2000;
  while currentHeight > 1000
    invariant currentHeight >= 1000
    invariant IsTall(currentHeight)
    decreases currentHeight
  {
    SoritesStep(currentHeight);
    currentHeight := currentHeight - 1;
  }
}