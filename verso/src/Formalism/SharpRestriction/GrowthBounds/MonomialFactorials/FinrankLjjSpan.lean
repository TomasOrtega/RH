import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemLevelsIff
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestRankLProved
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PadicIntegersEmbeddingMapPrime

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Lvl

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

/- English proof (translation)
Use `set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq`. Use `haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _`. Use `haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left`. Set `bY` to `Module.finBasis ℚ_[p] Yq`. Set `Ms` to `xiMons (r := r) G (G.B - jp)`.

Set `fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]` to `fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1`. Set `W` to `Submodule.span ℚ_[p] (Set.range fam)`. Establish `hle : Ljj p (r` using `r) G j jp ≤ W.restrictScalars ℤ_[p] := by`. Unfold `Ljj`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨y, hy, g, hg, rfl⟩`. Establish `hyY : y ∈ Yq` using `(Submodule.mem_inf.1 hy).1`. Establish `hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p]))`. Establish `h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq)` using `Submodule.mem_top`. Rewrite `h3` using `[← bY.span_eq]`.

Establish `h4` using `Submodule.mem_map_of_mem (f := Yq.subtype) h3`. Rewrite `h4` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h4`. Establish `hg2` using `xi_mem_span p G (G.B - jp) g hg`. Use `show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W`.

Establish `hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p] (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p]))`. Use `Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) : MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `this`. Establish `hmul` using `Submodule.mul_mem_mul hy3 hg2`.

Rewrite `hmul` using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_ hmul` and prove the remaining obligations. Introduce and unpack `_ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩`. Conclude with `⟨(a, ⟨m, hm⟩), rfl⟩`. Use `haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)`.

Establish `hle2 : Submodule.span ℚ_[p] (Ljj p (r` using `r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) ≤ W := by`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `hle hx`. Conclude with `Submodule.finiteDimensional_of_le hle2`.
-/
theorem Ljj_span_fd (j : Fin G.T.t → ℕ) (jp : ℕ) :
    FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
    unfold Ljj
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, g, hg, rfl⟩
    have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
    have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
      rw [← bY.span_eq] at h3
      have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
      rw [Submodule.map_span, ← Set.range_comp] at h4
      exact h4
    have hg2 := xi_mem_span p G (G.B - jp) g hg
    show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
    have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
        (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
        MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
    have hmul := Submodule.mul_mem_mul hy3 hg2
    rw [Submodule.span_mul_span] at hmul
    refine Submodule.span_mono ?_ hmul
    rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨(a, ⟨m, hm⟩), rfl⟩
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have hle2 : Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) ≤ W := by
    rw [Submodule.span_le]
    intro x hx
    exact hle hx
  exact Submodule.finiteDimensional_of_le hle2

/- English proof (translation)
The claim follows from `finrank_eq_span_gen (R := ℤ_[p]) (K := ℚ_[p]) _`.
-/
theorem finrank_Ljj_span (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) =
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) :=
  finrank_eq_span_gen (R := ℤ_[p]) (K := ℚ_[p]) _

end Lvl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
