import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatLevel

/- English proof (translation)
Establish `h' : ∑ i : Unit, (fun _ : Unit => f) i • (fun _ : Unit => y) i = 0` using `by simpa using h`. Take `⟨n, a, z, hx, ha⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'`. Use `⟨n, fun j => a () j, z, ?_, fun j => ?_⟩` and prove the remaining obligations. Simplify using `using hx ()`. Simplify using `using ha j`.
-/
theorem exists_trivial_of_smul_eq_zero {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Flat A M]
    (f : A) (y : M) (h : f • y = 0) :
    ∃ (n : ℕ) (u : Fin n → A) (v : Fin n → M), y = ∑ j, u j • v j ∧ ∀ j, f * u j = 0 := by
  classical
  have h' : ∑ i : Unit, (fun _ : Unit => f) i • (fun _ : Unit => y) i = 0 := by simpa using h
  obtain ⟨n, a, z, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  refine ⟨n, fun j => a () j, z, ?_, fun j => ?_⟩
  · simpa using hx ()
  · simpa using ha j

/- English proof (translation)
Set `_` to `c.toAlgebra`. Establish `: Module.Flat (W ⧸ Ideal.span {t ^ m}) B` using `hc`. Establish `hb : Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ b) • y = 0`. Rewrite using `[Algebra.smul_def]`. Conclude with `hy`.

Take `⟨n, u, v, hyv, hu⟩` from `exists_trivial_of_smul_eq_zero (A := W ⧸ Ideal.span {t ^ m}) (M := B) _ y hb`. Establish `key : ∀ j, ∃ s : W, u j = Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ a * s)`. Introduce `j`. Take `⟨w, hw⟩` from `Ideal.Quotient.mk_surjective (u j)`. Establish `h1` using `hu j`.

Rewrite `h1` using `[← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨s, hs⟩` from `h1`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[← hw]`. Use `congr 1`.

Establish `hb' : t ^ b ∈ nonZeroDivisors W` using `pow_mem ht b`. Establish `h2 : (w - t ^ a * s) * t ^ b = 0`. Rewrite `hs` using `[← h, pow_add]`. Take the linear combination `(-1 : W) * hs`. Conclude with `sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hb').mp h2)`.

Use `choose s hs using key`. Use `⟨∑ j, c (Ideal.Quotient.mk _ (s j)) * v j, ?_⟩` and prove the remaining obligations. Rewrite using `[hyv, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hs j, ← mul_assoc, ← map_mul, ← map_mul]`.

Both sides reduce to the same expression.
-/
theorem exists_mul_of_flat {W B : Type} [CommRing W] [CommRing B] {t : W} (ht : t ∈ nonZeroDivisors W)
    {a b m : ℕ} (h : a + b = m) (c : W ⧸ Ideal.span {t ^ m} →+* B) (hc : c.Flat) (y : B)
    (hy : c (Ideal.Quotient.mk _ (t ^ b)) * y = 0) : ∃ z, c (Ideal.Quotient.mk _ (t ^ a)) * z = y := by
  let _ := c.toAlgebra
  have : Module.Flat (W ⧸ Ideal.span {t ^ m}) B := hc
  have hb : Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ b) • y = 0 := by
    rw [Algebra.smul_def]
    exact hy
  obtain ⟨n, u, v, hyv, hu⟩ := exists_trivial_of_smul_eq_zero (A := W ⧸ Ideal.span {t ^ m}) (M := B) _ y hb
  have key : ∀ j, ∃ s : W, u j = Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ a * s) := by
    intro j
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (u j)
    have h1 := hu j
    rw [← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨s, hs⟩ := h1
    refine ⟨s, ?_⟩
    rw [← hw]
    congr 1
    have hb' : t ^ b ∈ nonZeroDivisors W := pow_mem ht b
    have h2 : (w - t ^ a * s) * t ^ b = 0 := by
      rw [← h, pow_add] at hs
      linear_combination (-1 : W) * hs
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hb').mp h2)
  choose s hs using key
  refine ⟨∑ j, c (Ideal.Quotient.mk _ (s j)) * v j, ?_⟩
  rw [hyv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, hs j, ← mul_assoc, ← map_mul, ← map_mul]
  rfl

/- English proof (translation)
Conclude with `mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)`.
-/
theorem natCast_mem_nonZeroDivisors (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    (l : WittVector l k) ∈ nonZeroDivisors (WittVector l k) := by
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Introduce `l _ k _ _ _ O _ F ρ m`. Use `show FlatL l m (CrystallineSemistableComparison.CH.cx (CrystallineSemistableComparison.CH.modF (CrystallineSemistableComparison.Pb.LsG.sW l F ρ m).A))`. Rewrite using `[CrystallineSemistableComparison.Pb.LsG.modF_sW]`. Introduce `i`. Use `⟨fun x => ?_, fun a b hab x hx => ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `s`. Establish `h0 : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m}) ((l : WittVector l k) ^ m) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)`. Express the relevant statement in the definitionally equal form `((s.obj (Fin.last i)).obj.i (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m}) ((l : WittVector l k) ^ m))) * (show (s.obj (Fin.last i)).obj.B from x s) = 0`. Rewrite using `[h0, map_zero, zero_mul]`. Establish `key : ∀ s : ComposableArrows (fl l F ρ m).FullSubcategory i, ∃ z : ((fl l F ρ m).ι ⋙ Wc.OM l F ρ m).obj (s.obj (Fin.last i)), (l : WittVector l k) ^ a • z = x s`.

Introduce `s`. Establish `hs : (s.obj (Fin.last i)).obj.i.Flat` using `(s.obj (Fin.last i)).property`. Establish `h0 : (l : WittVector l k) ^ b • x s = 0` using `congrFun hx s`. Take `⟨z, hz⟩` from `exists_mul_of_flat (natCast_mem_nonZeroDivisors l k) hab (s.obj (Fin.last i)).obj.i hs (x s) h0`. Conclude with `⟨z, hz⟩`.

Use `choose z hz using key`. Rewrite using `[CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]`. Conclude with `⟨z, funext fun s => hz s⟩`.
-/
theorem flatL_Kt : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  intro l _ k _ _ _ O _ F ρ m
  show FlatL l m (CrystallineSemistableComparison.CH.cx (CrystallineSemistableComparison.CH.modF (CrystallineSemistableComparison.Pb.LsG.sW l F ρ m).A))
  rw [CrystallineSemistableComparison.Pb.LsG.modF_sW]
  intro i
  refine ⟨fun x => ?_, fun a b hab x hx => ?_⟩
  · funext s
    have h0 : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m}) ((l : WittVector l k) ^ m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    change ((s.obj (Fin.last i)).obj.i (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})
      ((l : WittVector l k) ^ m))) * (show (s.obj (Fin.last i)).obj.B from x s) = 0
    rw [h0, map_zero, zero_mul]
  · have key : ∀ s : ComposableArrows (fl l F ρ m).FullSubcategory i,
        ∃ z : ((fl l F ρ m).ι ⋙ Wc.OM l F ρ m).obj (s.obj (Fin.last i)),
          (l : WittVector l k) ^ a • z = x s := by
      intro s
      have hs : (s.obj (Fin.last i)).obj.i.Flat := (s.obj (Fin.last i)).property
      have h0 : (l : WittVector l k) ^ b • x s = 0 := congrFun hx s
      obtain ⟨z, hz⟩ := exists_mul_of_flat (natCast_mem_nonZeroDivisors l k) hab
        (s.obj (Fin.last i)).obj.i hs (x s) h0
      exact ⟨z, hz⟩
    choose z hz using key
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    exact ⟨z, funext fun s => hz s⟩

end GlobalTheory.CompanionTheory.FlatLevel

end
