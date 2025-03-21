def part3indices [n] 't (conds: [n]i8) : {[n]i64 | \is ->
       FiltPartInv2 is (\_i -> true) (\i -> conds[i] == 1) (\i -> conds[i] == 2)
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
  in  inds

def partition3 [n] (p: f32 -> i8) (xs: [n]f32) : {[n]f32 | \ys -> true} =
  let conds = map (\x -> p x) xs
  let inds = part3indices conds
  in scatter (replicate n 0) inds xs
