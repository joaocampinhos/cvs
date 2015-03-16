method max(a:array<int>, numelems:int) returns(r:int)
  requires numelems > 0;
  requires a != null && a.Length >= numelems;
  ensures forall j :: 0 <= j < numelems ==> r >= a[j];
  ensures exists j :: 0 <= j < numelems && r == a[j];
{
  var i:int := 1;
  r := a[0];
  while(i<numelems)
  invariant 1 <= i <= numelems;
  invariant forall j :: 0 <= j < i ==> r >= a[j];
  invariant exists j :: 0 <= j < i && r == a[j];
  {
    if (a[i] > r) {
      r := a[i];
    }
    i:= i + 1;
  }
}
