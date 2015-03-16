method sum(a:array<int>,n:int) returns(s:int)
requires a != null && a.Length > n;
{
  var i:int := 0;
  while(i<n) {
    s := s + a[i];
    i := i + 1;
  }
}
