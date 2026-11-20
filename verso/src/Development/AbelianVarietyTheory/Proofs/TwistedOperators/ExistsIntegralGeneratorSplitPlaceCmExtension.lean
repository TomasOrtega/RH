import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVAlgebraMapMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitGen

open IsDedekindDomain.HeightOneSpectrum Polynomial

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB v hv`. Take `⟨P, Q, hPQ, hPv, hQv⟩` from `hv`. Establish `hσ` using `hB.cm`. Establish `h2 : Module.finrank F E = 2` using `hσ.2.2.1`. Use `haveI : IsGalois ℚ E := hB.galois`.

Use `haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E`. Establish `hPo : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E)` using `⟨P.isPrime, ⟨hPv.symm⟩⟩`. Establish `hQo : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 E)` using `⟨Q.isPrime, ⟨hQv.symm⟩⟩`. Take `⟨g, hg⟩` from `Ideal.exists_comap_galRestrict_eq (𝓞 F) F E (𝓞 E) hPo hQo`. Establish `hgQ : ∀ x : 𝓞 E, x ∈ Q.asIdeal → galRestrict (𝓞 F) F E (𝓞 E) g x ∈ P.asIdeal`.

Introduce `x hx`. Rewrite `hx` using `[← hg]`. Conclude with `hx`. Establish `hgE : ∀ x : 𝓞 E, ((galRestrict (𝓞 F) F E (𝓞 E) g x : 𝓞 E) : E) = g (x : E)` using `fun x => algebraMap_galRestrict_apply (𝓞 F) g x`. Establish `hne : P.asIdeal ≠ Q.asIdeal` using `fun h => hPQ (HeightOneSpectrum.ext h)`.

Establish `htop` using `Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal hne`. Take `⟨a, haP, j, hjQ, haj⟩` from `Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ P.asIdeal ⊔ Q.asIdeal)`. Establish `ha1Q : a - 1 ∈ Q.asIdeal`. Establish `: a - 1 = -j` using `by rw [← haj]; ring`. Rewrite using `[this]`.

Conclude with `neg_mem hjQ`. Establish `hga1 : galRestrict (𝓞 F) F E (𝓞 E) g a - 1 ∈ P.asIdeal`. Use `hgQ _ ha1Q` as an intermediate fact. Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis. Establish `h1P : (1 : 𝓞 E) ∉ P.asIdeal` using `fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`.

Establish `hga : g (a : E) ≠ a`. Introduce `h`. Apply `h1P` to reduce the goal to its premises. Establish `e : galRestrict (𝓞 F) F E (𝓞 E) g a = a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[hgE]`. Conclude with `h`. Use `P.asIdeal.sub_mem haP hga1` as an intermediate fact. Rewrite `this` using `[e]`. Simplify using `using this`.

Establish `hnot : (a : E) ∉ (algebraMap F E).range`. Introduce and unpack `⟨x, hx⟩`. Apply `hga` to reduce the goal to its premises. Rewrite using `[← hx, AlgEquiv.commutes]`. Establish `hi : IsIntegral (𝓞 F) a` using `Algebra.IsIntegral.isIntegral a`.

Establish `hmap : minpoly F (a : E) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F)` using `minpoly.isIntegrallyClosed_eq_field_fractions F E hi`. Establish `hdeg : (minpoly F (a : E)).natDegree = (minpoly (𝓞 F) a).natDegree`. Rewrite using `[hmap, (minpoly.monic hi).natDegree_map]`. Establish `hge : 2 ≤ (minpoly (𝓞 F) a).natDegree`. Rewrite using `[← hdeg]`.

Conclude with `(minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral _)).2 hnot`. Establish `hle : (minpoly F (a : E)).natDegree ≤ 2` using `h2 ▸ minpoly.natDegree_le (a : E)`. Take `⟨b, c, hbc⟩` from `isMonicOfDegree_two_iff.1 (⟨by omega, minpoly.monic hi⟩ : IsMonicOfDegree (minpoly (𝓞 F) a) 2)`. Establish `hq0 : a ^ 2 + algebraMap _ _ b * a + algebraMap _ _ c = 0`. Use `minpoly.aeval (𝓞 F) a` as an intermediate fact.

Rewrite `this` using `[hbc]`. Simplify using `using this`. Establish `hq : (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0`. Use `congrArg (algebraMap (𝓞 E) E) hq0` as an intermediate fact. Simplify using `only [map_add, map_mul, map_pow, map_zero] at this`.

Conclude with `this`. Establish `hli : LinearIndependent F ![(1 : E), a]`. Rewrite using `[LinearIndependent.pair_iff' one_ne_zero]`. Introduce `x hx`. Conclude with `hnot ⟨x, by rw [Algebra.algebraMap_eq_smul_one, hx]⟩`.

Set `Bs` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])`. Establish `hBs : ⇑Bs = ![(1 : E), a]` using `coe_basisOfLinearIndependentOfCardEqFinrank _ _`. Establish `hσa : σ (a : E) ≠ a`. Introduce `hfix`. Take `⟨x, hx⟩` from `GlobalTheory.InertUnitNorm.exists_ne_of_isCMExt σ hσ`.

Apply `hx` to reduce the goal to its premises. Establish `: σ.toLinearMap = LinearMap.id`. Use `Bs.ext fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify using `[hBs]`.

Simplify using `[hBs, hfix]`. Conclude with `congrArg (fun f : E →ₗ[F] E => f x) this`. Establish `hqσ : σ (a : E) ^ 2 + algebraMap F E (b : F) * σ a + algebraMap F E (c : F) = 0`. Use `congrArg σ hq` as an intermediate fact. Simplify `this` using `only [map_add, map_mul, map_pow, AlgHom.commutes, map_zero]`.

Establish `hconj : σ (a : E) = -algebraMap F E (b : F) - a`. Establish `hm : (σ (a : E) - a) * (σ a + a + algebraMap F E (b : F)) = 0`. Take the linear combination `hqσ - hq`. Break down `mul_eq_zero.1 hm with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) hσa`.

Take the linear combination `h`. Establish `hqg : g (a : E) ^ 2 + algebraMap F E (b : F) * g a + algebraMap F E (c : F) = 0`. Use `congrArg g hq` as an intermediate fact. Simplify `this` using `only [map_add, map_mul, map_pow, AlgEquiv.commutes, map_zero]`. Establish `hgconj : g (a : E) = -algebraMap F E (b : F) - a`.

Establish `hm : (g (a : E) - a) * (g a + a + algebraMap F E (b : F)) = 0`. Take the linear combination `hqg - hq`. Break down `mul_eq_zero.1 hm with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) hga`. Take the linear combination `h`.

Establish `hgO : galRestrict (𝓞 F) F E (𝓞 E) g a = -algebraMap (𝓞 F) (𝓞 E) b - a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hgE, hgconj]`. Simplify using `only [map_sub, map_neg]`. Both sides reduce to the same expression.

Use `⟨a, b, c, hq, hconj, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hPv, Ideal.mem_comap]`. Establish `e : algebraMap (𝓞 F) (𝓞 E) c = a * (-algebraMap (𝓞 F) (𝓞 E) b - a)`. Take the linear combination `hq0`. Rewrite using `[e]`.

Conclude with `P.asIdeal.mul_mem_right _ haP`. Introduce `hb`. Rewrite `hb` using `[← hPv, Ideal.mem_comap]`. Apply `h1P` to reduce the goal to its premises. Rewrite `hga1` using `[hgO]`.

Establish `e : (1 : 𝓞 E) = -(-algebraMap (𝓞 F) (𝓞 E) b - a - 1) - algebraMap (𝓞 F) (𝓞 E) b - a` using `by ring`. Rewrite using `[e]`. Conclude with `P.asIdeal.sub_mem (P.asIdeal.sub_mem (neg_mem hga1) hb) haP`.
-/
theorem exists_integral_gen_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∃ (a : 𝓞 E) (b c : 𝓞 F), (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 ∧
      σ (a : E) = -algebraMap F E (b : F) - a ∧ c ∈ v.asIdeal ∧ b ∉ v.asIdeal := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨P, Q, hPQ, hPv, hQv⟩ := hv
  have hσ := hB.cm
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : IsGalois ℚ E := hB.galois
  haveI : IsGalois F E := IsGalois.tower_top_of_isGalois ℚ F E
  have hPo : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨P.isPrime, ⟨hPv.symm⟩⟩
  have hQo : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨Q.isPrime, ⟨hQv.symm⟩⟩
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F E (𝓞 E) hPo hQo
  have hgQ : ∀ x : 𝓞 E, x ∈ Q.asIdeal → galRestrict (𝓞 F) F E (𝓞 E) g x ∈ P.asIdeal := by
    intro x hx
    rw [← hg] at hx
    exact hx
  have hgE : ∀ x : 𝓞 E, ((galRestrict (𝓞 F) F E (𝓞 E) g x : 𝓞 E) : E) = g (x : E) :=
    fun x => algebraMap_galRestrict_apply (𝓞 F) g x

  have hne : P.asIdeal ≠ Q.asIdeal := fun h => hPQ (HeightOneSpectrum.ext h)
  have htop := Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal hne
  obtain ⟨a, haP, j, hjQ, haj⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ P.asIdeal ⊔ Q.asIdeal)
  have ha1Q : a - 1 ∈ Q.asIdeal := by
    have : a - 1 = -j := by rw [← haj]; ring
    rw [this]; exact neg_mem hjQ
  have hga1 : galRestrict (𝓞 F) F E (𝓞 E) g a - 1 ∈ P.asIdeal := by
    have := hgQ _ ha1Q
    rwa [map_sub, map_one] at this
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hga : g (a : E) ≠ a := by
    intro h
    apply h1P
    have e : galRestrict (𝓞 F) F E (𝓞 E) g a = a := by
      apply RingOfIntegers.ext
      rw [hgE]; exact h
    have := P.asIdeal.sub_mem haP hga1
    rw [e] at this
    simpa using this
  have hnot : (a : E) ∉ (algebraMap F E).range := by
    rintro ⟨x, hx⟩
    apply hga
    rw [← hx, AlgEquiv.commutes]
  have hi : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hmap : minpoly F (a : E) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hi
  have hdeg : (minpoly F (a : E)).natDegree = (minpoly (𝓞 F) a).natDegree := by
    rw [hmap, (minpoly.monic hi).natDegree_map]
  have hge : 2 ≤ (minpoly (𝓞 F) a).natDegree := by
    rw [← hdeg]
    exact (minpoly.two_le_natDegree_iff (Algebra.IsIntegral.isIntegral _)).2 hnot
  have hle : (minpoly F (a : E)).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le (a : E)
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hi⟩ : IsMonicOfDegree (minpoly (𝓞 F) a) 2)
  have hq0 : a ^ 2 + algebraMap _ _ b * a + algebraMap _ _ c = 0 := by
    have := minpoly.aeval (𝓞 F) a
    rw [hbc] at this
    simpa using this
  have hq : (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 := by
    have := congrArg (algebraMap (𝓞 E) E) hq0
    simp only [map_add, map_mul, map_pow, map_zero] at this
    exact this
  have hli : LinearIndependent F ![(1 : E), a] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro x hx
    exact hnot ⟨x, by rw [Algebra.algebraMap_eq_smul_one, hx]⟩
  let Bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hBs : ⇑Bs = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hσa : σ (a : E) ≠ a := by
    intro hfix
    obtain ⟨x, hx⟩ := GlobalTheory.InertUnitNorm.exists_ne_of_isCMExt σ hσ
    apply hx
    have : σ.toLinearMap = LinearMap.id := by
      refine Bs.ext fun i => ?_
      fin_cases i
      · simp [hBs]
      · simp [hBs, hfix]
    exact congrArg (fun f : E →ₗ[F] E => f x) this
  have hqσ : σ (a : E) ^ 2 + algebraMap F E (b : F) * σ a + algebraMap F E (c : F) = 0 := by
    have := congrArg σ hq
    simpa only [map_add, map_mul, map_pow, AlgHom.commutes, map_zero] using this
  have hconj : σ (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (σ (a : E) - a) * (σ a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqσ - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hσa
    · linear_combination h
  have hqg : g (a : E) ^ 2 + algebraMap F E (b : F) * g a + algebraMap F E (c : F) = 0 := by
    have := congrArg g hq
    simpa only [map_add, map_mul, map_pow, AlgEquiv.commutes, map_zero] using this
  have hgconj : g (a : E) = -algebraMap F E (b : F) - a := by
    have hm : (g (a : E) - a) * (g a + a + algebraMap F E (b : F)) = 0 := by
      linear_combination hqg - hq
    rcases mul_eq_zero.1 hm with h | h
    · exact absurd (sub_eq_zero.1 h) hga
    · linear_combination h
  have hgO : galRestrict (𝓞 F) F E (𝓞 E) g a = -algebraMap (𝓞 F) (𝓞 E) b - a := by
    apply RingOfIntegers.ext
    rw [hgE, hgconj]
    simp only [map_sub, map_neg]
    rfl
  refine ⟨a, b, c, hq, hconj, ?_, ?_⟩
  ·
    rw [← hPv, Ideal.mem_comap]
    have e : algebraMap (𝓞 F) (𝓞 E) c = a * (-algebraMap (𝓞 F) (𝓞 E) b - a) := by
      linear_combination hq0
    rw [e]
    exact P.asIdeal.mul_mem_right _ haP
  · intro hb
    rw [← hPv, Ideal.mem_comap] at hb
    apply h1P
    rw [hgO] at hga1
    have e : (1 : 𝓞 E) = -(-algebraMap (𝓞 F) (𝓞 E) b - a - 1) - algebraMap (𝓞 F) (𝓞 E) b - a := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.sub_mem (neg_mem hga1) hb) haP

end GlobalTheory.SplitGen
