import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `hNV K L _ _ _ _ _ v d f e hf hne he hA hB c hc θ hθ`. Unfold `UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NormVal at hNV`. Establish `hv1 : ∀ {k : Type} [Field k] [ValuativeRel k] (a t : kˣ →* ℂˣ), vals {a} t = if IsUnram (a * t) then {(a * t) (unif k)} else 0`. Introduce `k _ _ a t`. Unfold `vals`.

Rewrite using `[Multiset.filter_singleton]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hadd : ∀ {k : Type} [Field k] [ValuativeRel k] (c1 c2 : Multiset (kˣ →* ℂˣ)) (t : kˣ →* ℂˣ), vals (c1 + c2) t = vals c1 t + vals c2 t`. Introduce `k _ _ c1 c2 t`. Simplify using `only [vals, Multiset.filter_add, Multiset.map_add]`.

Proceed by induction on `c using Multiset.induction_on with`. Consider the case `empty => simp [vals]`. Consider the case `cons a c ih`. Establish `hca : IsSmoothChar a` using `hc a (Multiset.mem_cons_self a c)`. Establish `ih'` using `ih (fun ξ h => hc ξ (Multiset.mem_cons_of_mem h))`.

Establish `hone : Multiset.map (fun x => x ^ f) (∑ j ∈ Finset.range d, vals {a} (θ * e j)) = f • ∑ w : PlacesOver L v, vals (Multiset.map (fun ξ => ξ.comp (nm w)) {a}) (θ.comp (nm w))`. Simplify using `only [Multiset.map_singleton, hv1, ← mul_assoc, ← MonoidHom.mul_comp]`. Use `set μ := a * θ with hμ`. Establish `hμs : IsSmoothChar μ`. Unfold `IsSmoothChar at hca hθ ⊢`.

Establish `hle : a.ker ⊓ θ.ker ≤ μ.ker`. Introduce `x hx`. Rewrite `hx` using `[Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.mem_ker, hμ, MonoidHom.mul_apply, hx.1, hx.2, mul_one]`. Conclude with `Subgroup.isOpen_mono hle (by rw [Subgroup.coe_inf]; exact hca.inter hθ)`.

Establish `hcomp : ∀ j (w : PlacesOver L v), (μ * e j).comp (nm w) = μ.comp (nm w)`. Introduce `j w`. Rewrite using `[MonoidHom.mul_comp, he j w, mul_one]`. Distinguish the cases in `hex : ∃ w : PlacesOver L v, IsUnram (μ.comp (nm w))`. Take `⟨w1, hw1⟩` from `hex`.

Establish `hall : ∀ w : PlacesOver L v, IsUnram (μ.comp (nm w))` using `fun w => hA w1 w μ hw1`. Establish `hcard` using `hB w1 μ hμs hw1`. Establish `hsumf : ∑ w' : PlacesOver L v, fdeg w' = Fintype.card (PlacesOver L v) * f`. Simplify using `only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]`. Establish `hfpos : 0 < f`.

Use `(hNV K L v w1 μ).2.2.1` as an intermediate fact. Rewrite `this` using `[hf w1]`. Then use the resulting hypothesis. Establish `hval : ∀ j, IsUnram (μ * e j) → ∀ w : PlacesOver L v, μ ((nm w) (unif (HeightOneSpectrum.adicCompletion L (w : HeightOneSpectrum (𝓞 L))))) = (μ * e j) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f`. Introduce `j hj w`. Establish `h1` using `((hNV K L v w (μ * e j)).1 hj).2`.

Establish `h2 : (e j) ((nm w) (unif (HeightOneSpectrum.adicCompletion L (w : HeightOneSpectrum (𝓞 L))))) = 1`. Use `congrArg (fun φ => φ (unif (HeightOneSpectrum.adicCompletion L (w : HeightOneSpectrum (𝓞 L))))) (he j w)` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[MonoidHom.mul_apply, h2, mul_one, hf w]`. Conclude with `h1`.

Establish `hpos : 0 < (Finset.filter (fun j => IsUnram (μ * e j)) (Finset.range d)).card`. Rewrite using `[hcard, hsumf]`. Conclude with `Nat.mul_pos (Fintype.card_pos_iff.mpr hne) hfpos`. Take `⟨j0, hj0⟩` from `Finset.card_pos.mp hpos`. Rewrite `hj0` using `[Finset.mem_filter]`.

Use `Eq.trans ((Multiset.eq_replicate (n := Fintype.card (PlacesOver L v) * f) (a := (μ * e j0) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f)).mpr ⟨?_, ?_⟩) ((Multiset.eq_replicate).mpr ⟨?_, ?_⟩).symm` and prove the remaining obligations. Rewrite using `[Multiset.card_map, Multiset.card_sum, ← hsumf, ← hcard, Finset.card_filter]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Introduce `b hb`.

Rewrite `hb` using `[Multiset.mem_map]`. Take `⟨x, hx, rfl⟩` from `hb`. Rewrite `hx` using `[Multiset.mem_sum]`. Take `⟨j, -, hxj⟩` from `hx`. Use `split_ifs at hxj with hj`.

Rewrite `hxj` using `[Multiset.mem_singleton]`. Substitute `hxj` using the available equality. Rewrite using `[← hval j hj w1, hval j0 hj0.2 w1]`. Simplify using `at hxj`. Simplify using `only [hall, ↓reduceIte]`.

Rewrite using `[Multiset.card_nsmul, Multiset.card_sum]`. Simplify using `[mul_comm]`. Introduce `b hb`. Simplify using `only [hall, ↓reduceIte] at hb`. Establish `hb'` using `Multiset.mem_of_mem_nsmul hb`.

Rewrite `hb'` using `[Multiset.mem_sum]`. Take `⟨w, -, hbw⟩` from `hb'`. Rewrite `hbw` using `[Multiset.mem_singleton]`. Rewrite using `[hbw, MonoidHom.comp_apply]`. Conclude with `hval j0 hj0.2 w`.

Use `push_neg at hex`. Establish `hno : ∀ j, ¬ IsUnram (μ * e j)`. Introduce `j hj`. Take `⟨w0⟩` from `hne`. Use `((hNV K L v w0 (μ * e j)).1 hj).1` as an intermediate fact.

Rewrite `this` using `[hcomp]`. Conclude with `hex w0 this`. Simplify using `[hno, hex]`. Rewrite using `[← Multiset.singleton_add]`. Simplify using `only [hadd, Multiset.map_add, Finset.sum_add_distrib, smul_add]`.

Rewrite using `[hone, ih']`.
-/
theorem UpperTheory.Gal.GamX.twValsOf :
    UpperTheory.Gal.GamX.TwValsOf := by
  intro hNV K L _ _ _ _ _ v d f e hf hne he hA hB c hc θ hθ
  unfold UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.NormVal at hNV
  have hv1 : ∀ {k : Type} [Field k] [ValuativeRel k] (a t : kˣ →* ℂˣ),
      vals {a} t = if IsUnram (a * t) then {(a * t) (unif k)} else 0 := by
    intro k _ _ a t
    unfold vals
    rw [Multiset.filter_singleton]
    split_ifs <;> simp
  have hadd : ∀ {k : Type} [Field k] [ValuativeRel k] (c1 c2 : Multiset (kˣ →* ℂˣ)) (t : kˣ →* ℂˣ),
      vals (c1 + c2) t = vals c1 t + vals c2 t := by
    intro k _ _ c1 c2 t
    simp only [vals, Multiset.filter_add, Multiset.map_add]
  induction c using Multiset.induction_on with
  | empty => simp [vals]
  | cons a c ih =>
    have hca : IsSmoothChar a := hc a (Multiset.mem_cons_self a c)
    have ih' := ih (fun ξ h => hc ξ (Multiset.mem_cons_of_mem h))
    have hone : Multiset.map (fun x => x ^ f) (∑ j ∈ Finset.range d, vals {a} (θ * e j)) =
        f • ∑ w : PlacesOver L v, vals (Multiset.map (fun ξ => ξ.comp (nm w)) {a}) (θ.comp (nm w)) := by
      simp only [Multiset.map_singleton, hv1, ← mul_assoc, ← MonoidHom.mul_comp]
      set μ := a * θ with hμ
      have hμs : IsSmoothChar μ := by
        unfold IsSmoothChar at hca hθ ⊢
        have hle : a.ker ⊓ θ.ker ≤ μ.ker := by
          intro x hx
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
          rw [MonoidHom.mem_ker, hμ, MonoidHom.mul_apply, hx.1, hx.2, mul_one]
        exact Subgroup.isOpen_mono hle (by rw [Subgroup.coe_inf]; exact hca.inter hθ)
      have hcomp : ∀ j (w : PlacesOver L v), (μ * e j).comp (nm w) = μ.comp (nm w) := by
        intro j w
        rw [MonoidHom.mul_comp, he j w, mul_one]
      by_cases hex : ∃ w : PlacesOver L v, IsUnram (μ.comp (nm w))
      · obtain ⟨w1, hw1⟩ := hex
        have hall : ∀ w : PlacesOver L v, IsUnram (μ.comp (nm w)) := fun w => hA w1 w μ hw1
        have hcard := hB w1 μ hμs hw1
        have hsumf : ∑ w' : PlacesOver L v, fdeg w' = Fintype.card (PlacesOver L v) * f := by
          simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        have hfpos : 0 < f := by
          have := (hNV K L v w1 μ).2.2.1
          rwa [hf w1] at this
        have hval : ∀ j, IsUnram (μ * e j) → ∀ w : PlacesOver L v,
            μ ((nm w) (unif (HeightOneSpectrum.adicCompletion L (w : HeightOneSpectrum (𝓞 L))))) =
              (μ * e j) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f := by
          intro j hj w
          have h1 := ((hNV K L v w (μ * e j)).1 hj).2
          have h2 : (e j) ((nm w) (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) = 1 := by
            have := congrArg (fun φ => φ (unif (HeightOneSpectrum.adicCompletion L
              (w : HeightOneSpectrum (𝓞 L))))) (he j w)
            simpa using this
          rw [MonoidHom.mul_apply, h2, mul_one, hf w] at h1
          exact h1
        have hpos : 0 < (Finset.filter (fun j => IsUnram (μ * e j)) (Finset.range d)).card := by
          rw [hcard, hsumf]
          exact Nat.mul_pos (Fintype.card_pos_iff.mpr hne) hfpos
        obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter] at hj0
        refine Eq.trans ((Multiset.eq_replicate (n := Fintype.card (PlacesOver L v) * f)
          (a := (μ * e j0) (unif (HeightOneSpectrum.adicCompletion K v)) ^ f)).mpr ⟨?_, ?_⟩)
          ((Multiset.eq_replicate).mpr ⟨?_, ?_⟩).symm
        · rw [Multiset.card_map, Multiset.card_sum, ← hsumf, ← hcard, Finset.card_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
        · intro b hb
          rw [Multiset.mem_map] at hb
          obtain ⟨x, hx, rfl⟩ := hb
          rw [Multiset.mem_sum] at hx
          obtain ⟨j, -, hxj⟩ := hx
          split_ifs at hxj with hj
          · rw [Multiset.mem_singleton] at hxj
            subst hxj
            rw [← hval j hj w1, hval j0 hj0.2 w1]
          · simp at hxj
        · simp only [hall, ↓reduceIte]
          rw [Multiset.card_nsmul, Multiset.card_sum]
          simp [mul_comm]
        · intro b hb
          simp only [hall, ↓reduceIte] at hb
          have hb' := Multiset.mem_of_mem_nsmul hb
          rw [Multiset.mem_sum] at hb'
          obtain ⟨w, -, hbw⟩ := hb'
          rw [Multiset.mem_singleton] at hbw
          rw [hbw, MonoidHom.comp_apply]
          exact hval j0 hj0.2 w
      · push_neg at hex
        have hno : ∀ j, ¬ IsUnram (μ * e j) := by
          intro j hj
          obtain ⟨w0⟩ := hne
          have := ((hNV K L v w0 (μ * e j)).1 hj).1
          rw [hcomp] at this
          exact hex w0 this
        simp [hno, hex]
    rw [← Multiset.singleton_add]
    simp only [hadd, Multiset.map_add, Finset.sum_add_distrib, smul_add]
    rw [hone, ih']
