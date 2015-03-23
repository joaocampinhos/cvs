method filled(a:array<int>, v:int, n:int) returns(s:bool)
  requires n >= 0;
  requires a != null && a.Length >= n;
  ensures s == true ==> forall j :: 0 <= j < n ==> a[j] == v;
  ensures s == false ==> exists j :: 0 <= j < n && a[j] != v;
{
  var i:int := 0;
  s := true;
  while(i<n)
  invariant 0 <= i <= n;
  invariant s == true ==> forall j :: 0 <= j < i ==> a[j] == v;
  invariant s == false ==> exists j :: 0 <= j < i && a[j] != v;
  {
    if (a[i] != v) {
      s := false;
      break;
    }
    i:= i + 1;
  }
}
