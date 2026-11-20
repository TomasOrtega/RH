import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.NatCastNeOfCop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopCocG

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ N _ x c d w g hH hLw hLift n r`. Take `⟨ws, hws⟩` from `hLw`. Establish `api` using `sApi Ω ε X l`. Establish `inv` using `sInvApi Ω ε X l N w`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases.

Substitute `hn` using the available equality. Conclude with `⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _, ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩`. Establish `hlp : l.Prime` using `Fact.out`. Establish `hL0 : r + n ≠ 0` using `by omega`. Establish `hM0 : N * l ^ (r + n) ≠ 0` using `mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)`.

Use `haveI : NeZero (N * l ^ (r + n)) := ⟨hM0⟩`. Establish `hMeq : topM l n r (N * N) = N * (N * l ^ (r + n))`. Unfold `topM`. Expand and normalize the polynomial expressions, which then agree. Use `haveI : NeZero (topM l n r (N * N)) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩`.

Establish `hLev : Lev l n N (N * l ^ (r + n)) (topM l n r (N * N)) g` using `⟨hMeq, ⟨l ^ (r + n), by ring⟩, ⟨N * l ^ r, by ring⟩, hn, hH.cop, hH.g0⟩`. Establish `hLv : Lv c d (N * l ^ (r + n))` using `hH.lv hlp.ne_zero (NeZero.ne N) rfl`. Establish `hdvdl : l ∣ N * l ^ (r + n)` using `Dvd.dvd.mul_left (dvd_pow_self l hL0) N`. Establish `hOk` using `ok_UV (M := N * l ^ (r + n)) (L := r + n) hlp hH.odd hH.cop (by omega) hdvdl x`. Take `⟨β, hβ, hcg⟩` from `sTopRel Ω ε X l n N (N * l ^ (r + n)) (topM l n r (N * N)) w g hLev hLift c d ws hws hLv _ _ hOk _ _ (ixU_toQ rfl x) (ixV_toQ rfl)`.

Conclude with `sTopCocG Ω ε X l n N _ _ w g hLev hLift _ _ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sTop0 :
    UpperTheory.V.Z.Kato.Nb.STop0 := by
  intro Ω _ _ _ ε X l _ N _ x c d w g hH hLw hLift n r
  obtain ⟨ws, hws⟩ := hLw
  have api := sApi Ω ε X l
  have inv := sInvApi Ω ε X l N w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _,
      ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩
  · have hlp : l.Prime := Fact.out
    have hL0 : r + n ≠ 0 := by omega
    have hM0 : N * l ^ (r + n) ≠ 0 := mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)
    haveI : NeZero (N * l ^ (r + n)) := ⟨hM0⟩
    have hMeq : topM l n r (N * N) = N * (N * l ^ (r + n)) := by
      unfold topM
      ring
    haveI : NeZero (topM l n r (N * N)) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩
    have hLev : Lev l n N (N * l ^ (r + n)) (topM l n r (N * N)) g :=
      ⟨hMeq, ⟨l ^ (r + n), by ring⟩, ⟨N * l ^ r, by ring⟩, hn, hH.cop, hH.g0⟩
    have hLv : Lv c d (N * l ^ (r + n)) := hH.lv hlp.ne_zero (NeZero.ne N) rfl
    have hdvdl : l ∣ N * l ^ (r + n) := Dvd.dvd.mul_left (dvd_pow_self l hL0) N
    have hOk := ok_UV (M := N * l ^ (r + n)) (L := r + n) hlp hH.odd hH.cop (by omega) hdvdl x
    obtain ⟨β, hβ, hcg⟩ := sTopRel Ω ε X l n N (N * l ^ (r + n)) (topM l n r (N * N)) w g hLev hLift c d ws hws hLv
      _ _ hOk _ _ (ixU_toQ rfl x) (ixV_toQ rfl)
    exact sTopCocG Ω ε X l n N _ _ w g hLev hLift _ _ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg
