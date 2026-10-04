import Meno.ZetaZero
import Meno.ZetaZeroEngine

/-! # The kernel sweep

The engine run behind the Davenport–Heilbronn certificate: the form
`3x² − 2xy + 2y²` over the square `[−78, 78]²`, cutoff `Q ≤ 10⁴`, centre
`2 − D0/U + i·T0/U ≈ 1.993941 + 23.019605i`, disc radius `0.03`, at
`U = 2⁶⁴`. Checked by `decide +kernel`. -/

namespace Meno

namespace DH

open Engine Epstein

/-- The fixed-point unit `2⁶⁴`. -/
abbrev U : ℕ := 18446744073709551616

instance : Fact (0 < U) := ⟨by decide⟩

/-- `3x² − 2xy + 2y²`, the non-principal form of discriminant `−20`. -/
def F : BinForm := ⟨3, -2, 2⟩

/-- The engine parameters: `log 2`, `π/2`, the centre, `σm = Re z₀ − 0.03`, and
the series lengths. -/
def P : Params U :=
  ⟨⟨12786308645202655646, 12786308645202655729⟩, ⟨28976077832308491369, 28976077832308491370⟩,
    111767042169775471, 424636773791830423690, 111767042169775471 + 553402322211286548,
    20, 14, 22⟩

theorem log2_eq : Iv.log2E (U := U) 40 = P.L2 := by decide +kernel

set_option maxHeartbeats 0 in
/-- **The sweep**, run by the kernel. -/
theorem sweep : boxAcc P (fun x y => F.q (x, y)) 78 10000 = ⟨true,
    ⟨10395081477835070830, 10395081477835082676⟩, ⟨10395202536762722168, 10395202536762735196⟩,
    ⟨3315706241898497806, 3315706241898511052⟩, ⟨3315719068817312378, 3315719068817326548⟩,
    ⟨10155433712425335738, 10155433712425446350⟩, ⟨14734054119732011564, 14734054119732108580⟩,
    ⟨6534583528861529408, 6534583528861635572⟩, ⟨4679911583944239380, 4679911583944344084⟩,
    60119912310279762518⟩ := by
  decide +kernel

end DH

end Meno
