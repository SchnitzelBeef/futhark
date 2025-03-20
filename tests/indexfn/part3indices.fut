def sum [n] (xs: [n]i64) =
  if n > 0 then (scan (+) 0 xs)[n-1] else 0

def part3indices [n] 't (conds: [n]i8) : {(i64,i64,[n]i64) | \(s1,s2,is) ->
    BijectiveRCD is (0, n-1) (0, n-1)
      && s1 == sum (map (\c -> if c == 1 then 1 else 0 ) conds)
      && s2 == s1 + sum (map (\c -> if c == 2 then 1 else 0 ) conds)
  } =
  let tflags = map (\c -> if c == 1 then 1 else 0 ) conds
  let eflags = map (\c -> if c == 2 then 1 else 0 ) conds

  let indsL = scan (+) 0 tflags
  let indsE = scan (+) 0 eflags

  let s1 = if n > 0 then indsL[n-1] else 0
  let s2 = if n > 0 then indsE[n-1] else 0

  let inds  = map4 (\ c indL indE i ->
                        if c == 1 then indL - 1
                        else if c == 2 then s1 + indE - 1
                        else s1 + s2 + i - indsL[i] - indsE[i]
                   ) conds indsL indsE (iota n)
  in  (s1, s1 + s2, inds)
