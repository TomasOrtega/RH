import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Spanpsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SimpSpan

open UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA in
/- English proof (translation)
Introduce `hRP hRI hG L _ _ _ N σ hσ p t ht`. Apply `spanpsd` to reduce the goal to its premises. Introduce `k hk hzero`. Take `⟨k', hk'q, hk'P⟩` from `hRP L N σ hσ k`. Take `⟨hk'psd, hk'0⟩` from `hk'P hk`.

Apply `hk'0` to reduce the goal to its premises. Use `ConeExtensionAcyclic.simp_span (hG L N σ hσ).locFin p t ht k' hk'psd ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hM : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (y : Lat L N) = 1`. Introduce `j`.

Use `hy j` as an intermediate fact. Rewrite `this` using `[qr_apply]`. Conclude with `this`. Establish `hinvq : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (sLat σ (y : Lat L N)) = 1`. Introduce `j`.

Rewrite using `[((hRI L N σ hσ).2 _ (t j).1.2).1 (y : Lat L N)]`. Conclude with `hM j`. Rewrite using `[qr_apply, hk'q, hzero _ hM, hzero _ hinvq]`. Evaluate the numerical expressions.
-/
theorem UpperTheory.real_span_of_good_real_form :
    UpperTheory.V.Af.BA.RePart → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.GoodRe → UpperTheory.V.Af.BA.SpanRe := by
  intro hRP hRI hG L _ _ _ N σ hσ p t ht
  apply spanpsd
  intro k hk hzero
  obtain ⟨k', hk'q, hk'P⟩ := hRP L N σ hσ k
  obtain ⟨hk'psd, hk'0⟩ := hk'P hk
  apply hk'0
  refine ConeExtensionAcyclic.simp_span (hG L N σ hσ).locFin p t ht k' hk'psd ?_
  intro y hy
  have hM : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (y : Lat L N) = 1 := by
    intro j
    have := hy j
    rw [qr_apply] at this
    exact this
  have hinvq : ∀ (j : Fin (p + 1)), q (((t j : HR L N)) : HS L N) (sLat σ (y : Lat L N)) = 1 := by
    intro j
    rw [((hRI L N σ hσ).2 _ (t j).1.2).1 (y : Lat L N)]
    exact hM j
  rw [qr_apply, hk'q, hzero _ hM, hzero _ hinvq]
  norm_num
