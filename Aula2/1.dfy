method memcpy(a:array<int>, b:array<int>, n:int)
modifies b;
requires a != null && b != null;
requires n >= 0 && a.Length >= n && b.Length >= n;
ensures forall j :: 0 <= j < n ==> a[j] == b[j];
{
  var i:int := 0;
  while (i<n)
  invariant 0 <= i <= n;
  invariant forall j :: 0 <= j < i ==> a[j] == b[j];
  {
    b[i] := a[i];
    i := i + 1;
  }
}
