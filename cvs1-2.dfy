method memcpy(a:array<int>, b:array<int>, n:int)
requires a != null && b != null && a.Length >= n && b.Length >= n;
modifies b;
{
  var i:int := 0;
  while (i<n) {
    b[i] := a[i];
    i := i + 1;
  }
}

