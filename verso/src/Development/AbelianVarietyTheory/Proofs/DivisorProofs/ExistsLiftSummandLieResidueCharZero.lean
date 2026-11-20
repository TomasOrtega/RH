import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparabilityElementOfTraceNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersTraceMulLeftNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderTraceFormNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalEigenIdempotentsOfSeparabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSeparabilityAverageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.HTSummand

/- English proof (translation)
Introduce `p _ D R _ b C _ _ _ I hI hp tR H _ _ _ _ ρ _ e he heρ hω F hIF hFO heF hE' hLie`. Establish `hunitN : ∀ n : ℕ, n ≠ 0 → IsUnit (n : C)`. Introduce `n hn`. Take `⟨k, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).one_lt.ne'`. Establish `hcop : m.Coprime p` using `Nat.coprime_comm.mp (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)`.

Establish `h2 : IsUnit (tR (m : R))` using `(b.unit m hcop).map tR`. Rewrite `h2` using `[map_natCast]`. Use `push_cast`. Conclude with `(hp.pow k).mul h2`. Establish `hunitZ : ∀ N : ℤ, N ≠ 0 → IsUnit (N : C)`.

Introduce `N hN`. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg N`. Conclude with `hunitN n (by rintro rfl; simp at hN)` after adjusting the coercions. Use the proof step `push_cast; exact (hunitN n (by rintro rfl; simp at hN)).neg`. Take `⟨NF, kF, u, v, hNF, huv, hcomF⟩` from `GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' (𝓞 D.F) (GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero D.F)`.

Use `haveI := D.freeO`. Use `haveI := D.finO`. Take `⟨NO, kO, x, y, hNO, hxy, hcomO⟩` from `GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' D.O (GlobalTheory.T.harrisTaylorOrder_traceForm_nondegenerate p D)`. Take `⟨φ, hφc, hφφ, hφcomm, hφF, hφmod⟩` from `GlobalTheory.T.exists_orthogonal_eigen_idempotents_of_separability R C (𝓞 D.F) tR D.a b.t b.comax NF kF u v huv hcomF (hunitZ NF hNF) H (ρ.comp (algebraMap (𝓞 D.F) D.O))`. Establish `hFO' : ∀ c, ∀ z ∈ F, (ρ.comp (algebraMap (𝓞 D.F) D.O)) c z ∈ F` using `fun c z hz => hFO _ z hz`.

Use `set f : Module.End C H := ∑ i, φ i with hfdef`. Establish `hfapp : ∀ z, f z = ∑ i, φ i z` using `fun z => by rw [hfdef, LinearMap.sum_apply]`. Establish `hf : f * f = f`. Rewrite using `[hfdef, Finset.sum_mul_sum]`. Simplify using `only [hφφ]`.

Conclude with `Finset.sum_congr rfl fun i _ => by simp`. Establish `hcommF : ∀ g : Module.End C H, (∀ c : 𝓞 D.F, g * ρ (algebraMap _ D.O c) = ρ (algebraMap _ D.O c) * g) → g * f = f * g`. Introduce `g hg`. Establish `hg' : ∀ c, g * (ρ.comp (algebraMap (𝓞 D.F) D.O)) c = (ρ.comp (algebraMap (𝓞 D.F) D.O)) c * g` using `fun c => hg _`. Rewrite using `[hfdef, Finset.mul_sum, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => hφcomm g hg' i`. Establish `hef : e * f = f * e` using `hcommF e fun c => (heρ _).symm`. Establish `hρf : ∀ c : D.O, ρ c * f = f * ρ c` using `fun c => hcommF (ρ c) fun c' => by`. Rewrite using `[← map_mul, ← map_mul, Algebra.commutes]`. Establish `hfF : ∀ z ∈ F, f z ∈ F` using `fun z hz => by`.

Rewrite using `[hfapp]`. Conclude with `Submodule.sum_mem F fun i _ => hφF F hFO' i z hz`. Use `set ε : Module.End C H := f * e with hεdef`. Establish `hεapp : ∀ z, ε z = f (e z)` using `fun z => rfl`. Establish `hε : ε * ε = ε`.

Combine the equalities or inequalities in the displayed calculation. Establish `hρε : ∀ c, ρ c * ε = ε * ρ c` using `fun c => by`. Combine the equalities or inequalities in the displayed calculation. Establish `hFε : ∀ z ∈ F, ε z ∈ F` using `fun z hz => hfF _ (heF z hz)`. Take `⟨π, hππ, hπρ, hπε, hεπ, hA, hB⟩` from `GlobalTheory.T.exists_idempotent_separability_average C D.O I hI NO kO x y hxy hcomO (hunitZ NO hNO) H ρ ε hε hρε F hIF hFO hFε hE'`.

Establish `hεε : ∀ z, ε (ε z) = ε z` using `fun z => LinearMap.congr_fun hε z`. Establish `hπε' : ∀ z, π (ε z) = π z` using `fun z => LinearMap.congr_fun hπε z`. Establish `hεπ' : ∀ z, ε (π z) = π z` using `fun z => LinearMap.congr_fun hεπ z`. Establish `hππ' : ∀ z, π (π z) = π z` using `fun z => LinearMap.congr_fun hππ z`. Establish `hfπ : ∀ z, f (π z) = π z` using `fun z => by`.

Rewrite using `[← hεπ' z, hεapp, ← hεapp]`. Use `LinearMap.congr_fun hf (e (π z))` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[hεapp, this]`. Establish `hπP : ∀ z, π z ∈ LinearMap.range e` using `fun z => ⟨f (π z), by`.

Use `LinearMap.congr_fun hef (π z)` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Conclude with `this.trans (hεπ' z)⟩`. Establish `heP : ∀ d ∈ LinearMap.range e, e d = d`. Introduce and unpack `d ⟨z, rfl⟩`.

Conclude with `LinearMap.congr_fun he z`. Establish `hfP : ∀ d ∈ LinearMap.range e, d - f d ∈ F`. Introduce `d hd`. Take `⟨w, hw1, hw2⟩` from `hLie d hd`. Establish `hfw : ∀ i, f (w i) - w i ∈ F`.

Introduce `i`. Establish `hs` using `Submodule.sum_mem F fun j (_ : j ∈ Finset.univ) => hφmod F hFO' i (w i) (hw1 i) j`. Rewrite `hs` using `[Finset.sum_sub_distrib, Finset.sum_ite_eq']`. Simplify `hs` using `[hfapp]`. Establish `key : d - f d = (d - ∑ i, w i) - f (d - ∑ i, w i) - ∑ i, (f (w i) - w i)`.

Simplify using `only [map_sub, map_sum, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Conclude with `F.sub_mem (F.sub_mem hw2 (hfF _ hw2)) (Submodule.sum_mem F fun i _ => hfw i)`. Establish `hGmem : ∀ d ∈ LinearMap.range e, d - π d ∈ LinearMap.range e ⊓ LinearMap.ker π` using `fun d hd => ⟨Submodule.sub_mem _ hd (hπP d), by simp [hππ']⟩`.

Use `⟨LinearMap.range e ⊓ LinearMap.ker π, LinearMap.range π, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `z hz`. Take `⟨⟨-, hz1⟩, ⟨w, rfl⟩⟩` from `hz`. Use `replace hz1 : π (π w) = 0 := hz1`.

Rewrite using `[Submodule.mem_bot, ← hππ' w]`. Conclude with `hz1`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sup_le inf_le_left (by rintro _ ⟨z, rfl⟩; exact hπP z)`. Introduce `d hd`.

Conclude with `Submodule.mem_sup.2 ⟨d - π d, hGmem d hd, π d, ⟨d, rfl⟩, sub_add_cancel d (π d)⟩`. Introduce and unpack `c z ⟨⟨w, rfl⟩, hz⟩`. Use `Submodule.mem_inf.2 ⟨LinearMap.mem_range.2 ⟨ρ c w, ?_⟩, ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun (heρ c) w` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`.

Conclude with `this.symm`. Use `replace hz : π (e w) = 0 := hz show π (ρ c (e w)) = 0`. Use `LinearMap.congr_fun (hπρ c) (e w)` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[← this, hz, map_zero]`.

Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le ?_ (inf_le_inf_right _ hIF)` and prove the remaining obligations. Introduce and unpack `z ⟨hzP, hz⟩`. Use `replace hz : π z = 0 := hz`. Use `Submodule.mem_inf.2 ⟨?_, hzP⟩` and prove the remaining obligations.

Establish `h1` using `hfP z hzP`. Establish `h2` using `hA (ε z) (hεε z)`. Rewrite `h2` using `[hπε', hz, sub_zero]`. Establish `: z = (z - f z) + ε z` using `by rw [hεapp, heP z hzP]; abel`. Rewrite using `[this]`.

Conclude with `F.add_mem h1 h2`. Introduce and unpack `z ⟨hzF, hzP⟩`. Use `Submodule.mem_sup.2 ⟨z - π z, hGmem z hzP, π z, Submodule.mem_inf.2 ⟨?_, hπP z⟩, sub_add_cancel z (π z)⟩` and prove the remaining obligations. Rewrite using `[← hπε']`. Conclude with `hB (ε z) (hFε z hzF) (hεε z)`.

Introduce `d hd`. Use `⟨fun i => φ i (π d), fun i c => ?_, ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun (hφc i c) (π d)` as an intermediate fact. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, RingHom.comp_apply] at this`. Rewrite using `[this, sub_self]`.

Conclude with `Submodule.zero_mem _`. Establish `: ∑ i, φ i (π d) = π d` using `by rw [← hfapp]; exact hfπ d`. Rewrite using `[this]`. Conclude with `hGmem d hd`.
-/
theorem liftSummand_residueCharZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (I : Ideal C), I ^ 2 = ⊥ → IsUnit (p : C) → ∀ (tR : R →+* C) (H : Type 1) [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H] (ρ : D.O →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf (ρ.comp (algebraMap (𝓞 D.F) D.O)); Module.Projective (C ⊗[ℤ] 𝓞 D.F) H) → ∀ (e : Module.End C H), e * e = e → (∀ c, ρ c * e = e * ρ c) → (∀ x, ρ (algebraMap (𝓞 D.F) D.O D.ω) (e x) = tR b.ρ • e x) → ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ (c : D.O), ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, e x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → (∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧ d - ∑ i, w i ∈ F) → ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : D.O), ∀ x ∈ G, ρ c x ∈ G) ∧ G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧ ∀ d ∈ LinearMap.range e, ∃ w : Fin D.a → H, (∀ i (c : 𝓞 D.F), ρ (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by

  intro p _ D R _ b C _ _ _ I hI hp tR H _ _ _ _ ρ _ e he heρ hω F hIF hFO heF hE' hLie
  have hunitN : ∀ n : ℕ, n ≠ 0 → IsUnit (n : C) := by
    intro n hn
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).one_lt.ne'
    have hcop : m.Coprime p := Nat.coprime_comm.mp (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
    have h2 : IsUnit (tR (m : R)) := (b.unit m hcop).map tR
    rw [map_natCast] at h2
    push_cast
    exact (hp.pow k).mul h2
  have hunitZ : ∀ N : ℤ, N ≠ 0 → IsUnit (N : C) := by
    intro N hN
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
    · exact_mod_cast hunitN n (by rintro rfl; simp at hN)
    · push_cast; exact (hunitN n (by rintro rfl; simp at hN)).neg
  obtain ⟨NF, kF, u, v, hNF, huv, hcomF⟩ := GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' (𝓞 D.F) (GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero D.F)
  haveI := D.freeO; haveI := D.finO
  obtain ⟨NO, kO, x, y, hNO, hxy, hcomO⟩ := GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' D.O (GlobalTheory.T.harrisTaylorOrder_traceForm_nondegenerate p D)
  obtain ⟨φ, hφc, hφφ, hφcomm, hφF, hφmod⟩ := GlobalTheory.T.exists_orthogonal_eigen_idempotents_of_separability R C (𝓞 D.F) tR D.a b.t b.comax NF kF u v huv hcomF
    (hunitZ NF hNF) H (ρ.comp (algebraMap (𝓞 D.F) D.O))
  have hFO' : ∀ c, ∀ z ∈ F, (ρ.comp (algebraMap (𝓞 D.F) D.O)) c z ∈ F := fun c z hz => hFO _ z hz
  set f : Module.End C H := ∑ i, φ i with hfdef
  have hfapp : ∀ z, f z = ∑ i, φ i z := fun z => by rw [hfdef, LinearMap.sum_apply]
  have hf : f * f = f := by
    rw [hfdef, Finset.sum_mul_sum]
    simp only [hφφ]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hcommF : ∀ g : Module.End C H, (∀ c : 𝓞 D.F, g * ρ (algebraMap _ D.O c) = ρ (algebraMap _ D.O c) * g) → g * f = f * g := by
    intro g hg
    have hg' : ∀ c, g * (ρ.comp (algebraMap (𝓞 D.F) D.O)) c = (ρ.comp (algebraMap (𝓞 D.F) D.O)) c * g :=
      fun c => hg _
    rw [hfdef, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hφcomm g hg' i
  have hef : e * f = f * e := hcommF e fun c => (heρ _).symm
  have hρf : ∀ c : D.O, ρ c * f = f * ρ c := fun c => hcommF (ρ c) fun c' => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hfF : ∀ z ∈ F, f z ∈ F := fun z hz => by
    rw [hfapp]; exact Submodule.sum_mem F fun i _ => hφF F hFO' i z hz
  set ε : Module.End C H := f * e with hεdef
  have hεapp : ∀ z, ε z = f (e z) := fun z => rfl
  have hε : ε * ε = ε := by
    calc f * e * (f * e) = f * ((e * f) * e) := by simp only [_root_.mul_assoc]
      _ = f * ((f * e) * e) := by rw [hef]
      _ = (f * f) * (e * e) := by simp only [_root_.mul_assoc]
      _ = f * e := by rw [hf, he]
  have hρε : ∀ c, ρ c * ε = ε * ρ c := fun c => by
    calc ρ c * (f * e) = (ρ c * f) * e := by rw [_root_.mul_assoc]
      _ = f * (ρ c * e) := by rw [hρf, _root_.mul_assoc]
      _ = f * e * ρ c := by rw [heρ, _root_.mul_assoc]
  have hFε : ∀ z ∈ F, ε z ∈ F := fun z hz => hfF _ (heF z hz)
  obtain ⟨π, hππ, hπρ, hπε, hεπ, hA, hB⟩ := GlobalTheory.T.exists_idempotent_separability_average C D.O I hI NO kO x y hxy hcomO (hunitZ NO hNO) H ρ ε hε hρε
    F hIF hFO hFε hE'
  have hεε : ∀ z, ε (ε z) = ε z := fun z => LinearMap.congr_fun hε z
  have hπε' : ∀ z, π (ε z) = π z := fun z => LinearMap.congr_fun hπε z
  have hεπ' : ∀ z, ε (π z) = π z := fun z => LinearMap.congr_fun hεπ z
  have hππ' : ∀ z, π (π z) = π z := fun z => LinearMap.congr_fun hππ z
  have hfπ : ∀ z, f (π z) = π z := fun z => by
    rw [← hεπ' z, hεapp, ← hεapp]
    have := LinearMap.congr_fun hf (e (π z))
    simp only [Module.End.mul_apply] at this
    rw [hεapp, this]
  have hπP : ∀ z, π z ∈ LinearMap.range e := fun z => ⟨f (π z), by
    have := LinearMap.congr_fun hef (π z)
    simp only [Module.End.mul_apply] at this
    exact this.trans (hεπ' z)⟩
  have heP : ∀ d ∈ LinearMap.range e, e d = d := by
    rintro d ⟨z, rfl⟩
    exact LinearMap.congr_fun he z
  have hfP : ∀ d ∈ LinearMap.range e, d - f d ∈ F := by
    intro d hd
    obtain ⟨w, hw1, hw2⟩ := hLie d hd
    have hfw : ∀ i, f (w i) - w i ∈ F := by
      intro i
      have hs := Submodule.sum_mem F fun j (_ : j ∈ Finset.univ) => hφmod F hFO' i (w i) (hw1 i) j
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq'] at hs
      simpa [hfapp] using hs
    have key : d - f d = (d - ∑ i, w i) - f (d - ∑ i, w i) - ∑ i, (f (w i) - w i) := by
      simp only [map_sub, map_sum, Finset.sum_sub_distrib]; abel
    rw [key]
    exact F.sub_mem (F.sub_mem hw2 (hfF _ hw2)) (Submodule.sum_mem F fun i _ => hfw i)
  have hGmem : ∀ d ∈ LinearMap.range e, d - π d ∈ LinearMap.range e ⊓ LinearMap.ker π := fun d hd =>
    ⟨Submodule.sub_mem _ hd (hπP d), by simp [hππ']⟩
  refine ⟨LinearMap.range e ⊓ LinearMap.ker π, LinearMap.range π, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨-, hz1⟩, ⟨w, rfl⟩⟩ := hz
    replace hz1 : π (π w) = 0 := hz1
    rw [Submodule.mem_bot, ← hππ' w]; exact hz1
  · apply le_antisymm
    · exact sup_le inf_le_left (by rintro _ ⟨z, rfl⟩; exact hπP z)
    · intro d hd
      exact Submodule.mem_sup.2 ⟨d - π d, hGmem d hd, π d, ⟨d, rfl⟩, sub_add_cancel d (π d)⟩
  · rintro c z ⟨⟨w, rfl⟩, hz⟩
    refine Submodule.mem_inf.2 ⟨LinearMap.mem_range.2 ⟨ρ c w, ?_⟩, ?_⟩
    · have := LinearMap.congr_fun (heρ c) w
      simp only [Module.End.mul_apply] at this
      exact this.symm
    · replace hz : π (e w) = 0 := hz
      show π (ρ c (e w)) = 0
      have := LinearMap.congr_fun (hπρ c) (e w)
      simp only [Module.End.mul_apply] at this
      rw [← this, hz, map_zero]
  · apply le_antisymm
    · refine sup_le ?_ (inf_le_inf_right _ hIF)
      rintro z ⟨hzP, hz⟩
      replace hz : π z = 0 := hz
      refine Submodule.mem_inf.2 ⟨?_, hzP⟩
      have h1 := hfP z hzP
      have h2 := hA (ε z) (hεε z)
      rw [hπε', hz, sub_zero] at h2
      have : z = (z - f z) + ε z := by rw [hεapp, heP z hzP]; abel
      rw [this]; exact F.add_mem h1 h2
    · rintro z ⟨hzF, hzP⟩
      refine Submodule.mem_sup.2 ⟨z - π z, hGmem z hzP, π z, Submodule.mem_inf.2 ⟨?_, hπP z⟩, sub_add_cancel z (π z)⟩
      rw [← hπε']; exact hB (ε z) (hFε z hzF) (hεε z)
  · intro d hd
    refine ⟨fun i => φ i (π d), fun i c => ?_, ?_⟩
    · have := LinearMap.congr_fun (hφc i c) (π d)
      simp only [Module.End.mul_apply, LinearMap.smul_apply, RingHom.comp_apply] at this
      rw [this, sub_self]; exact Submodule.zero_mem _
    · have : ∑ i, φ i (π d) = π d := by rw [← hfapp]; exact hfπ d
      rw [this]; exact hGmem d hd

end GlobalTheory.HTSummand
