method find(v:int, a:array<int>, numelems:int) returns(r:int)
  requires numelems > 0;
  requires a != null && a.Length >= numelems;
  ensures (r == -1 && forall j :: 0 <= j < numelems ==> a[j] != v) ||  (0 <= r < numelems && a[r] == v);
{
  var i:int := 0;
  r := -1;
  while(i<numelems)
  invariant 0 <= i <= numelems;
  invariant (r == -1 && forall j :: 0 <= j < i ==> a[j] != v) ||  (0 <= r < i && a[r] == v);
  {
    if (a[i] == v) {
      r := i;
      break;
    }
    i:= i + 1;
  }
}
