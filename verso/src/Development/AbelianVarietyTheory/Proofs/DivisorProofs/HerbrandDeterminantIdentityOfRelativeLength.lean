import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValIntStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbDet

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

/- English proof (translation)
Introduce `h0`. Take `⟨w, hw, hw0⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h0`. Apply `hw` to reduce the goal to its premises. Establish `hs : ∑ i, w i • u i = 0`. Use function extensionality and compare the values at `j`.

Use `congr_fun hw0 j` as an intermediate fact. Simplify `this` using `only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.of_apply]`. Conclude with `funext (Fintype.linearIndependent_iff.1 hu w hs)`.
-/
theorem det_ne_zero_of_linearIndependent {n : ℕ} (u : Fin n → (Fin n → Int0 v))
    (hu : LinearIndependent (Int0 v) u) : (Matrix.of u).det ≠ 0 := by
  intro h0
  obtain ⟨w, hw, hw0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  apply hw
  have hs : ∑ i, w i • u i = 0 := by
    funext j
    have := congr_fun hw0 j
    simpa only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.of_apply] using this
  exact funext (Fintype.linearIndependent_iff.1 hu w hs)

variable {S : Type} [Fintype S] [DecidableEq S] {a : S → Int0 v} {N : ℕ}
  {Fil : Submodule (RS a) (Fin N → RS a)} {τ : S}

/- English proof (translation)
Rewrite `hz` using `[← hE8]`. Take `⟨y, hy, hyz⟩` from `hz`. Establish `hzy : z - y ∈ Fil.restrictScalars (Int0 v)`. Establish `h0 : proj a Fil (z - y) = 0` using `by rw [map_sub, hyz, sub_self]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).1 h0`.

Simplify using `using add_mem (hE10 hzy) hy`.
-/
theorem mem_preEig_of_proj_mem
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ) (z : Fin N → RS a)
    (hz : proj a Fil z ∈ eigSub a τ ((Fin N → RS a) ⧸ Fil)) : z ∈ preEig a Fil τ := by
  rw [← hE8] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hzy : z - y ∈ Fil.restrictScalars (Int0 v) := by
    have h0 : proj a Fil (z - y) = 0 := by rw [map_sub, hyz, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0
  simpa using add_mem (hE10 hzy) hy

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `w hw`. Rewrite `hw` using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at hw`. Establish `hmem : ∑ j, w (Sum.inr j) • (f j : Fin N → Int0 v) ∈ (Fil.restrictScalars (Int0 v)).map (comp a N τ)` using `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (f j).2`.

Take `⟨φ, hφ, hφe⟩` from `hmem`. Establish `hzX : ∑ i, w (Sum.inl i) • x i ∈ preEig a Fil τ` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)`. Establish `hcomp : comp a N τ (∑ i, w (Sum.inl i) • x i + φ) = 0`. Rewrite using `[map_add, map_sum, hφe]`. Simplify `hw` using `[map_smul]`.

Establish `hzφ : ∑ i, w (Sum.inl i) • x i + φ ∈ Fil.restrictScalars (Int0 v)` using `hE4 ⟨add_mem hzX (hE10 hφ), hcomp⟩`. Establish `hz : ∑ i, w (Sum.inl i) • x i ∈ Fil.restrictScalars (Int0 v)`. Simplify using `using sub_mem hzφ hφ`. Establish `hprojz : proj a Fil (∑ i, w (Sum.inl i) • x i) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hz`. Establish `hl : ∑ i, w (Sum.inl i) • l i = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite `hprojz` using `[map_sum]`. Simplify using `only [map_smul, hx] at hprojz`. Simplify using `using hprojz`. Establish `hα` using `Fintype.linearIndependent_iff.1 l.linearIndependent _ hl`.

Establish `hf : ∑ j, w (Sum.inr j) • f j = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hα, zero_smul, Finset.sum_const_zero, zero_add] at hw`. Simplify using `using hw`. Establish `hβ` using `Fintype.linearIndependent_iff.1 f.linearIndependent _ hf`.

Introduce and unpack `(i | j)`. Conclude with `hα i`. Conclude with `hβ j`.
-/
theorem linearIndependent_comb {ι κ : Type} [Fintype ι] [Fintype κ]
    (hE4 : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v))
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ)
    (l : Basis ι (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : ι → (Fin N → RS a)) (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (hxX : ∀ i, x i ∈ preEig a Fil τ)
    (f : Basis κ (Int0 v) (eigQuot a Fil τ)) :
    LinearIndependent (Int0 v)
      (Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v))) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  rw [Fintype.sum_sum_type] at hw
  simp only [Sum.elim_inl, Sum.elim_inr] at hw
  have hmem : ∑ j, w (Sum.inr j) • (f j : Fin N → Int0 v) ∈
      (Fil.restrictScalars (Int0 v)).map (comp a N τ) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (f j).2
  obtain ⟨φ, hφ, hφe⟩ := hmem
  have hzX : ∑ i, w (Sum.inl i) • x i ∈ preEig a Fil τ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)
  have hcomp : comp a N τ (∑ i, w (Sum.inl i) • x i + φ) = 0 := by
    rw [map_add, map_sum, hφe]
    simpa [map_smul] using hw
  have hzφ : ∑ i, w (Sum.inl i) • x i + φ ∈ Fil.restrictScalars (Int0 v) :=
    hE4 ⟨add_mem hzX (hE10 hφ), hcomp⟩
  have hz : ∑ i, w (Sum.inl i) • x i ∈ Fil.restrictScalars (Int0 v) := by
    simpa using sub_mem hzφ hφ
  have hprojz : proj a Fil (∑ i, w (Sum.inl i) • x i) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hz
  have hl : ∑ i, w (Sum.inl i) • l i = 0 := by
    apply Subtype.ext
    rw [map_sum] at hprojz
    simp only [map_smul, hx] at hprojz
    simpa using hprojz
  have hα := Fintype.linearIndependent_iff.1 l.linearIndependent _ hl
  have hf : ∑ j, w (Sum.inr j) • f j = 0 := by
    apply Subtype.ext
    simp only [hα, zero_smul, Finset.sum_const_zero, zero_add] at hw
    simpa using hw
  have hβ := Fintype.linearIndependent_iff.1 f.linearIndependent _ hf
  rintro (i | j)
  · exact hα i
  · exact hβ j

/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `hy`. Establish `hpz : proj a Fil z ∈ eigSub a τ ((Fin N → RS a) ⧸ Fil)`. Rewrite using `[← hE8]`. Conclude with `Submodule.mem_map_of_mem hz`. Establish `hl` using `congrArg Subtype.val (l.sum_repr ⟨proj a Fil z, hpz⟩)`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at hl`. Establish `hsum : proj a Fil (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) = 0`. Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul, hx]`. Rewrite using `[hl, sub_self]`.

Establish `hw : z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i ∈ Fil.restrictScalars (Int0 v)` using `(Submodule.Quotient.mk_eq_zero _).1 hsum`. Establish `hfw : comp a N τ (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) ∈ eigQuot a Fil τ` using `Submodule.mem_map_of_mem hw`. Establish `h2` using `congrArg Subtype.val (f.sum_repr ⟨_, hfw⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h2`. Use `⟨Sum.elim (l.repr ⟨proj a Fil z, hpz⟩) (f.repr ⟨_, hfw⟩), ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr]`. Establish `h3 : comp a N τ (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) = comp a N τ z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • comp a N τ (x i)`. Simplify using `only [map_sub, map_sum, map_smul]`. Conclude with `eq_sub_iff_add_eq'.1 (h2.trans h3)`.
-/
theorem span_comb {ι κ : Type} [Fintype ι] [Fintype κ]
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (l : Basis ι (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : ι → (Fin N → RS a)) (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (f : Basis κ (Int0 v) (eigQuot a Fil τ)) (y : Fin N → Int0 v)
    (hy : y ∈ (preEig a Fil τ).map (comp a N τ)) :
    ∃ c : ι ⊕ κ → Int0 v, ∑ s, c s •
      (Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v))) s = y := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hpz : proj a Fil z ∈ eigSub a τ ((Fin N → RS a) ⧸ Fil) := by
    rw [← hE8]; exact Submodule.mem_map_of_mem hz
  have hl := congrArg Subtype.val (l.sum_repr ⟨proj a Fil z, hpz⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hl
  have hsum : proj a Fil (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul, hx]
    rw [hl, sub_self]
  have hw : z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i ∈ Fil.restrictScalars (Int0 v) :=
    (Submodule.Quotient.mk_eq_zero _).1 hsum
  have hfw : comp a N τ (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) ∈ eigQuot a Fil τ :=
    Submodule.mem_map_of_mem hw
  have h2 := congrArg Subtype.val (f.sum_repr ⟨_, hfw⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  refine ⟨Sum.elim (l.repr ⟨proj a Fil z, hpz⟩) (f.repr ⟨_, hfw⟩), ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have h3 : comp a N τ (z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • x i) =
      comp a N τ z - ∑ i, l.repr ⟨proj a Fil z, hpz⟩ i • comp a N τ (x i) := by
    simp only [map_sub, map_sum, map_smul]
  exact eq_sub_iff_add_eq'.1 (h2.trans h3)

end GlobalTheory.HerbDet

namespace GlobalTheory.HerbDet

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
variable {S : Type} [Fintype S] [DecidableEq S] {a : S → Int0 v} {N : ℕ}
  {Fil : Submodule (RS a) (Fin N → RS a)} {τ : S}

/- English proof (translation)
Establish `hxX : ∀ i, x i ∈ preEig a Fil τ` using `fun i => mem_preEig_of_proj_mem hE8 hE10 (x i) (by rw [hx i]; exact (l i).2)`. Establish `hmem : ∀ s, Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v)) s ∈ (preEig a Fil τ).map (comp a N τ)`. Introduce and unpack `(i | j)`. Conclude with `Submodule.mem_map_of_mem (hxX i)`. Conclude with `Submodule.map_mono hE10 (f j).2`.

Establish `hli` using `linearIndependent_comb hE4 hE10 l x hx hxX f`. Establish `hli' : LinearIndependent (Int0 v) (fun s => (⟨_, hmem s⟩ : (preEig a Fil τ).map (comp a N τ)))`. Apply `LinearIndependent.of_comp ((preEig a Fil τ).map (comp a N τ)).subtype` to reduce the goal to its premises. Conclude with `hli`. Use `⟨Basis.mk hli' ?_, fun s => by rw [Basis.mk_apply]⟩` and prove the remaining obligations.

Introduce `y _`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `span_comb hE8 l x hx f y y.2`. Conclude with `⟨c, Subtype.ext (by simpa using hc)⟩`.
-/
theorem exists_basis_comb {ι κ : Type} [Fintype ι] [Fintype κ]
    (hE4 : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v))
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ)
    (l : Basis ι (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : ι → (Fin N → RS a)) (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (f : Basis κ (Int0 v) (eigQuot a Fil τ)) :
    ∃ b : Basis (ι ⊕ κ) (Int0 v) ((preEig a Fil τ).map (comp a N τ)),
      ∀ s, (b s : Fin N → Int0 v) =
        Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v)) s := by
  have hxX : ∀ i, x i ∈ preEig a Fil τ := fun i =>
    mem_preEig_of_proj_mem hE8 hE10 (x i) (by rw [hx i]; exact (l i).2)
  have hmem : ∀ s, Sum.elim (fun i => comp a N τ (x i)) (fun j => (f j : Fin N → Int0 v)) s ∈
      (preEig a Fil τ).map (comp a N τ) := by
    rintro (i | j)
    · exact Submodule.mem_map_of_mem (hxX i)
    · exact Submodule.map_mono hE10 (f j).2
  have hli := linearIndependent_comb hE4 hE10 l x hx hxX f
  have hli' : LinearIndependent (Int0 v)
      (fun s => (⟨_, hmem s⟩ : (preEig a Fil τ).map (comp a N τ))) := by
    apply LinearIndependent.of_comp ((preEig a Fil τ).map (comp a N τ)).subtype
    exact hli
  refine ⟨Basis.mk hli' ?_, fun s => by rw [Basis.mk_apply]⟩
  intro y _
  rw [Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨c, hc⟩ := span_comb hE8 l x hx f y y.2
  exact ⟨c, Subtype.ext (by simpa using hc)⟩

/- English proof (translation)
Establish `hli : LinearIndependent (Int0 v) (fun k => comp a N τ (h k : Fin N → RS a))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `w hw`. Establish `hm : ((∑ k, w k • h k : eigSub a τ (Fin N → RS a)) : Fin N → RS a) ∈ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ)`. Use `Submodule.mem_inf.2 ⟨Subtype.mem _, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, Submodule.coe_sum, map_sum]`. Simplify `hw` using `[map_smul]`. Rewrite `hm` using `[hE6, Submodule.mem_bot]`. Conclude with `Fintype.linearIndependent_iff.1 h.linearIndependent w (Subtype.ext hm)`. Establish `hmem : ∀ k, comp a N τ (h k : Fin N → RS a) ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ)` using `fun k => Submodule.mem_map_of_mem (h k).2`.

Establish `hli' : LinearIndependent (Int0 v) (fun k => (⟨_, hmem k⟩ : (eigSub a τ (Fin N → RS a)).map (comp a N τ)))`. Apply `LinearIndependent.of_comp ((eigSub a τ (Fin N → RS a)).map (comp a N τ)).subtype` to reduce the goal to its premises. Conclude with `hli`. Use `⟨Basis.mk hli' ?_, fun k => by rw [Basis.mk_apply]⟩` and prove the remaining obligations. Introduce and unpack `⟨_, z, hz, rfl⟩ _`.

Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Use `⟨h.repr ⟨z, hz⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg Subtype.val (h.sum_repr ⟨z, hz⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h1`. Establish `h2` using `congrArg (comp a N τ) h1`.

Simplify using `only [map_sum, map_smul] at h2`. Simplify using `using h2`.
-/
theorem exists_basis_image {ι : Type} [Fintype ι]
    (hE6 : eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥)
    (h : Basis ι (Int0 v) (eigSub a τ (Fin N → RS a))) :
    ∃ b : Basis ι (Int0 v) ((eigSub a τ (Fin N → RS a)).map (comp a N τ)),
      ∀ k, (b k : Fin N → Int0 v) = comp a N τ (h k : Fin N → RS a) := by
  have hli : LinearIndependent (Int0 v) (fun k => comp a N τ (h k : Fin N → RS a)) := by
    rw [Fintype.linearIndependent_iff]
    intro w hw
    have hm : ((∑ k, w k • h k : eigSub a τ (Fin N → RS a)) : Fin N → RS a) ∈
        eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) := by
      refine Submodule.mem_inf.2 ⟨Subtype.mem _, ?_⟩
      rw [LinearMap.mem_ker, Submodule.coe_sum, map_sum]
      simpa [map_smul] using hw
    rw [hE6, Submodule.mem_bot] at hm
    exact Fintype.linearIndependent_iff.1 h.linearIndependent w (Subtype.ext hm)
  have hmem : ∀ k, comp a N τ (h k : Fin N → RS a) ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ) :=
    fun k => Submodule.mem_map_of_mem (h k).2
  have hli' : LinearIndependent (Int0 v)
      (fun k => (⟨_, hmem k⟩ : (eigSub a τ (Fin N → RS a)).map (comp a N τ))) := by
    apply LinearIndependent.of_comp ((eigSub a τ (Fin N → RS a)).map (comp a N τ)).subtype
    exact hli
  refine ⟨Basis.mk hli' ?_, fun k => by rw [Basis.mk_apply]⟩
  rintro ⟨_, z, hz, rfl⟩ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨h.repr ⟨z, hz⟩, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val (h.sum_repr ⟨z, hz⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
  have h2 := congrArg (comp a N τ) h1
  simp only [map_sum, map_smul] at h2
  simpa using h2

/- English proof (translation)
Establish `hex : ∀ i : Fin N, ∃ z ∈ eigSub a τ (Fin N → RS a), comp a N τ z = d • (Pi.single i 1 : Fin N → Int0 v)`. Introduce `i`. Establish `: d • (Pi.single i 1 : Fin N → Int0 v) ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ)`. Rewrite using `[hE7]`. Conclude with `⟨Pi.single i 1, trivial, rfl⟩`.

Take `⟨z, hz, hze⟩` from `this`. Conclude with `⟨z, hz, hze⟩`. Use `choose z hz hze using hex`. Establish `hinj : ∀ y ∈ eigSub a τ (Fin N → RS a), comp a N τ y = 0 → y = 0`. Introduce `y hy hy0`.

Establish `: y ∈ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ)` using `⟨hy, hy0⟩`. Rewrite `this` using `[hE6, Submodule.mem_bot]`. Then use the resulting hypothesis. Establish `hcomb : ∀ w : Fin N → Int0 v, comp a N τ (∑ i, w i • z i) = d • w`. Introduce `w`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, hze]`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, mul_comm, mul_left_comm]`. Establish `hli : LinearIndependent (Int0 v) (fun i => (⟨z i, hz i⟩ : eigSub a τ (Fin N → RS a)))`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `w hw`. Establish `h0 : ∑ i, w i • z i = 0`. Use `congrArg Subtype.val hw` as an intermediate fact. Simplify using `using this`. Establish `h1 : d • w = 0` using `by rw [← hcomb, h0, map_zero]`.

Establish `h2 : w = 0` using `(smul_eq_zero.1 h1).resolve_left hd`. Introduce `i`. Rewrite using `[h2]`. Both sides reduce to the same expression. Use `⟨Basis.mk hli ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, hy⟩ _`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Establish `hy' : comp a N τ y ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ)` using `Submodule.mem_map_of_mem hy`. Rewrite `hy'` using `[hE7]`. Take `⟨u, -, hu⟩` from `hy'`.

Use `⟨u, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hmem : y - ∑ i, u i • z i ∈ eigSub a τ (Fin N → RS a)` using `sub_mem hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz i))`. Establish `hc : comp a N τ (y - ∑ i, u i • z i) = 0`. Rewrite using `[map_sub, hcomb, ← hu]`. Simplify using the standard rewrite rules.

Use `hinj _ hmem hc` as an intermediate fact. Rewrite `this` using `[sub_eq_zero]`. Simplify using `using this.symm`.
-/
theorem exists_basis_eigSub (d : Int0 v) (hd : d ≠ 0)
    (hE6 : eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥)
    (hE7 : (eigSub a τ (Fin N → RS a)).map (comp a N τ) =
      (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d)) :
    Nonempty (Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a))) := by
  have hex : ∀ i : Fin N, ∃ z ∈ eigSub a τ (Fin N → RS a),
      comp a N τ z = d • (Pi.single i 1 : Fin N → Int0 v) := by
    intro i
    have : d • (Pi.single i 1 : Fin N → Int0 v) ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
      rw [hE7]; exact ⟨Pi.single i 1, trivial, rfl⟩
    obtain ⟨z, hz, hze⟩ := this
    exact ⟨z, hz, hze⟩
  choose z hz hze using hex
  have hinj : ∀ y ∈ eigSub a τ (Fin N → RS a), comp a N τ y = 0 → y = 0 := by
    intro y hy hy0
    have : y ∈ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) := ⟨hy, hy0⟩
    rwa [hE6, Submodule.mem_bot] at this
  have hcomb : ∀ w : Fin N → Int0 v,
      comp a N τ (∑ i, w i • z i) = d • w := by
    intro w
    rw [map_sum]
    simp only [map_smul, hze]
    funext j
    simp [Finset.sum_apply, Pi.single_apply, mul_comm, mul_left_comm]
  have hli : LinearIndependent (Int0 v) (fun i => (⟨z i, hz i⟩ : eigSub a τ (Fin N → RS a))) := by
    rw [Fintype.linearIndependent_iff]
    intro w hw
    have h0 : ∑ i, w i • z i = 0 := by
      have := congrArg Subtype.val hw
      simpa using this
    have h1 : d • w = 0 := by rw [← hcomb, h0, map_zero]
    have h2 : w = 0 := (smul_eq_zero.1 h1).resolve_left hd
    intro i; rw [h2]; rfl
  refine ⟨Basis.mk hli ?_⟩
  rintro ⟨y, hy⟩ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  have hy' : comp a N τ y ∈ (eigSub a τ (Fin N → RS a)).map (comp a N τ) :=
    Submodule.mem_map_of_mem hy
  rw [hE7] at hy'
  obtain ⟨u, -, hu⟩ := hy'
  refine ⟨u, Subtype.ext ?_⟩
  have hmem : y - ∑ i, u i • z i ∈ eigSub a τ (Fin N → RS a) :=
    sub_mem hy (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz i))
  have hc : comp a N τ (y - ∑ i, u i • z i) = 0 := by
    rw [map_sub, hcomb, ← hu]; simp
  have := hinj _ hmem hc
  rw [sub_eq_zero] at this
  simpa using this.symm

end GlobalTheory.HerbDet

namespace GlobalTheory.HerbDet

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
variable {S : Type} [Fintype S] [DecidableEq S] {a : S → Int0 v} {N : ℕ}
  {Fil : Submodule (RS a) (Fin N → RS a)} {τ : S}

/- English proof (translation)
Set `A : Matrix (Fin N) (Fin N) (Int0 v)` to `fun i k => bX.repr ⟨(bX' k : Fin N → Int0 v), hle (bX' k).2⟩ i`. Establish `hA : ∀ k, ((bX' k : Fin N → Int0 v)) = ∑ i, A i k • (bX i : Fin N → Int0 v)`. Introduce `k`. Use `congrArg Subtype.val (bX.sum_repr ⟨(bX' k : Fin N → Int0 v), hle (bX' k).2⟩)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`.

Conclude with `this.symm`. Establish `hM : (Matrix.of fun k : Fin N => (bX' k : Fin N → Int0 v)) = A.transpose * Matrix.of fun k : Fin N => (bX k : Fin N → Int0 v)`. Use extensionality with `k j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, Matrix.transpose_apply]`.

Rewrite using `[hA k, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Establish `hli : LinearIndependent (Int0 v) (fun k => (bX k : Fin N → Int0 v))` using `bX.linearIndependent.map' X.subtype (Submodule.ker_subtype _)`. Establish `hli' : LinearIndependent (Int0 v) (fun k => (bX' k : Fin N → Int0 v))` using `bX'.linearIndependent.map' X'.subtype (Submodule.ker_subtype _)`. Establish `hM0` using `det_ne_zero_of_linearIndependent _ hli`.

Establish `hM0'` using `det_ne_zero_of_linearIndependent _ hli'`. Establish `hA0 : A.det ≠ 0`. Introduce `h0`. Apply `hM0'` to reduce the goal to its premises. Rewrite using `[hM, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul]`.

Establish `hvA : v (A.det : C) ≠ ⊤`. Rewrite using `[Ne, AddValuation.top_iff]`. Conclude with `fun h0 => hA0 (Subtype.ext h0)`. Establish `hRL' : RelLen v X' X ((v (A.det : C)).untop hvA)` using `⟨N, bX, bX', A, hA, by rw [WithTop.coe_untop]⟩`. Establish `hrr` using `RelLen.unique v hRL hRL'`.

Use `⟨(A.det : C), ?_, hM0, ?_⟩` and prove the remaining obligations. Rewrite using `[hrr, WithTop.coe_untop]`. Rewrite using `[hM, Matrix.det_mul, Matrix.det_transpose, Subring.coe_mul]`.
-/
theorem det_eq_mul_of_relLen {X' X : Submodule (Int0 v) (Fin N → Int0 v)} (hle : X' ≤ X) {r : ℝ}
    (hRL : RelLen v X' X r) (bX : Basis (Fin N) (Int0 v) X) (bX' : Basis (Fin N) (Int0 v) X') :
    ∃ c : C, v c = r ∧
      (Matrix.of fun k : Fin N => (bX k : Fin N → Int0 v)).det ≠ 0 ∧
      ((Matrix.of fun k : Fin N => (bX' k : Fin N → Int0 v)).det : C) =
        c * ((Matrix.of fun k : Fin N => (bX k : Fin N → Int0 v)).det : C) := by
  let A : Matrix (Fin N) (Fin N) (Int0 v) := fun i k => bX.repr ⟨(bX' k : Fin N → Int0 v), hle (bX' k).2⟩ i
  have hA : ∀ k, ((bX' k : Fin N → Int0 v)) = ∑ i, A i k • (bX i : Fin N → Int0 v) := by
    intro k
    have := congrArg Subtype.val (bX.sum_repr ⟨(bX' k : Fin N → Int0 v), hle (bX' k).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hM : (Matrix.of fun k : Fin N => (bX' k : Fin N → Int0 v)) =
      A.transpose * Matrix.of fun k : Fin N => (bX k : Fin N → Int0 v) := by
    ext k j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    rw [hA k, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hli : LinearIndependent (Int0 v) (fun k => (bX k : Fin N → Int0 v)) :=
    bX.linearIndependent.map' X.subtype (Submodule.ker_subtype _)
  have hli' : LinearIndependent (Int0 v) (fun k => (bX' k : Fin N → Int0 v)) :=
    bX'.linearIndependent.map' X'.subtype (Submodule.ker_subtype _)
  have hM0 := det_ne_zero_of_linearIndependent _ hli
  have hM0' := det_ne_zero_of_linearIndependent _ hli'
  have hA0 : A.det ≠ 0 := by
    intro h0
    apply hM0'
    rw [hM, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul]
  have hvA : v (A.det : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact fun h0 => hA0 (Subtype.ext h0)
  have hRL' : RelLen v X' X ((v (A.det : C)).untop hvA) :=
    ⟨N, bX, bX', A, hA, by rw [WithTop.coe_untop]⟩
  have hrr := RelLen.unique v hRL hRL'
  refine ⟨(A.det : C), ?_, hM0, ?_⟩
  · rw [hrr, WithTop.coe_untop]
  · rw [hM, Matrix.det_mul, Matrix.det_transpose, Subring.coe_mul]

/- English proof (translation)
Take `⟨bL0, hbL0⟩` from `exists_basis_comb hE4 hE8 hE10 l x hx f`. Take `⟨bh, hbh⟩` from `exists_basis_image hE6 h`. Establish `hbL : (fun k => ((bL0.reindex e.symm) k : Fin N → Int0 v)) = fun k => Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)`. Use function extensionality and compare the values at `k`. Use `hbL0 (e k)` as an intermediate fact.

Simplify `this` using `only [Basis.reindex_apply, Equiv.symm_symm]`. Establish `hbh' : (fun k => (bh k : Fin N → Int0 v)) = fun k => comp a N τ (h k : Fin N → RS a)`. Use function extensionality and compare the values at `hbh`. Use `det_eq_mul_of_relLen (Submodule.map_mono hE9) hRL (bL0.reindex e.symm) bh` as an intermediate fact. Rewrite `this` using `[hbL, hbh']`.

Conclude with `this`.
-/
theorem det_part
    (hE4 : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v))
    (hE6 : eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥)
    (hE8 : (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil))
    (hE9 : eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ)
    (hE10 : Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ) {r : ℝ}
    (hRL : RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ))
      ((preEig a Fil τ).map (comp a N τ)) r) {p j : ℕ}
    (h : Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a)))
    (l : Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
    (x : Fin p → (Fin N → RS a))
    (hx : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
    (f : Basis (Fin j) (Int0 v) (eigQuot a Fil τ)) (e : Fin N ≃ Fin p ⊕ Fin j) :
    ∃ c : C, v c = r ∧
      (Matrix.of fun k : Fin N =>
        Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det ≠ 0 ∧
      ((Matrix.of fun k : Fin N => comp a N τ (h k : Fin N → RS a)).det : C) =
        c * ((Matrix.of fun k : Fin N =>
          Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det : C) := by
  obtain ⟨bL0, hbL0⟩ := exists_basis_comb hE4 hE8 hE10 l x hx f
  obtain ⟨bh, hbh⟩ := exists_basis_image hE6 h
  have hbL : (fun k => ((bL0.reindex e.symm) k : Fin N → Int0 v)) = fun k =>
      Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k) := by
    funext k
    have := hbL0 (e k)
    simpa only [Basis.reindex_apply, Equiv.symm_symm] using this
  have hbh' : (fun k => (bh k : Fin N → Int0 v)) = fun k => comp a N τ (h k : Fin N → RS a) :=
    funext hbh
  have := det_eq_mul_of_relLen (Submodule.map_mono hE9) hRL (bL0.reindex e.symm) bh
  rw [hbL, hbh'] at this
  exact this

/- English proof (translation)
Introduce `C _ v S _ _ a ha N Fil hsat τ r hr hRL`. Take `⟨hd, -, -, hE4, -, hE6, hE7, hE8, hE9, hE10, -, -⟩` from `GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hsat τ`. Take `⟨hfFil, -, -, -, hfLie, -, -⟩` from `GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hsat τ`. Use `haveI : Module.IsTorsionFree (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) := Module.IsTorsionFree.of_smul_eq_zero fun c m hcm => by`. Distinguish the cases in `hc : c = 0`.

Conclude with `Or.inl hc`. Use `right`. Take `⟨m, hm⟩` from `m`. Apply `Subtype.ext` to reduce the goal to its premises. Proceed by induction on `m using Submodule.Quotient.induction_on with`.

Consider the case `H z`. Establish `h0 : (c • Submodule.Quotient.mk z : (Fin N → RS a) ⧸ Fil) = 0` using `congrArg Subtype.val hcm`. Rewrite `h0` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `show Submodule.Quotient.mk z = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `hsat c z hc h0`. Use `haveI := hfLie`. Use `haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))`. Use `haveI := hfFil`. Use `haveI hfQ : Module.Finite (Int0 v) (eigQuot a Fil τ) := Module.Finite.map (Fil.restrictScalars (Int0 v)) (comp a N τ)`.

Use `haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (eigQuot a Fil τ)`. Establish `hrk : finrank (Int0 v) (eigQuot a Fil τ) = eigRank v a Fil τ` using `GlobalTheory.T.finrank_int0_submodule_eq_finrank_span C v N (eigQuot a Fil τ) hfQ`. Establish `bF` using `Module.finBasisOfFinrankEq (Int0 v) (eigQuot a Fil τ) hrk`. Establish `bLie` using `Module.finBasis (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))`. Take `⟨bH⟩` from `exists_basis_eigSub (ev a τ (cofac a τ)) hd hE6 hE7`.

Use `⟨finrank (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)), ?_, ⟨bH⟩, ⟨bLie⟩, ⟨bF⟩, ?_⟩` and prove the remaining obligations. Take `⟨n, b1, b1', -, -, -⟩` from `hRL`. Establish `hlift : ∀ i, ∃ z : Fin N → RS a, proj a Fil z = (bLie i : (Fin N → RS a) ⧸ Fil)` using `fun i => Submodule.mkQ_surjective Fil _`. Use `choose x hx using hlift`. Take `⟨bL, -⟩` from `exists_basis_comb hE4 hE8 hE10 bLie x hx bF`.

Take `⟨bHi, -⟩` from `exists_basis_image hE6 bH`. Establish `h1` using `Fintype.card_congr (bL.indexEquiv b1)`. Establish `h2` using `Fintype.card_congr (bHi.indexEquiv b1')`. Simplify using `only [Fintype.card_sum, Fintype.card_fin] at h1 h2`. Use linear arithmetic over natural numbers and integers.

Introduce `h l x hx f e`. Take `⟨c, hc, h1, h2⟩` from `det_part hE4 hE6 hE8 hE9 hE10 hRL h l x hx f e`. Conclude with `⟨c, hc.trans hr, h1, h2⟩`.
-/
theorem detIdentity_of_relLen : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type)
    [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a →
    ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)),
      (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) →
      ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ →
        RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ))
          ((preEig a Fil τ).map (comp a N τ)) r →
        DetIdentity v a Fil τ := by
  intro C _ v S _ _ a ha N Fil hsat τ r hr hRL
  obtain ⟨hd, -, -, hE4, -, hE6, hE7, hE8, hE9, hE10, -, -⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hsat τ
  obtain ⟨hfFil, -, -, -, hfLie, -, -⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hsat τ

  haveI : Module.IsTorsionFree (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) :=
    Module.IsTorsionFree.of_smul_eq_zero fun c m hcm => by
      by_cases hc : c = 0
      · exact Or.inl hc
      right
      obtain ⟨m, hm⟩ := m
      apply Subtype.ext
      induction m using Submodule.Quotient.induction_on with
      | H z =>
        have h0 : (c • Submodule.Quotient.mk z : (Fin N → RS a) ⧸ Fil) = 0 :=
          congrArg Subtype.val hcm
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
        show Submodule.Quotient.mk z = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact hsat c z hc h0
  haveI := hfLie
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v)
    (eigSub a τ ((Fin N → RS a) ⧸ Fil))

  haveI := hfFil
  haveI hfQ : Module.Finite (Int0 v) (eigQuot a Fil τ) :=
    Module.Finite.map (Fil.restrictScalars (Int0 v)) (comp a N τ)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) (eigQuot a Fil τ)
  have hrk : finrank (Int0 v) (eigQuot a Fil τ) = eigRank v a Fil τ :=
    GlobalTheory.T.finrank_int0_submodule_eq_finrank_span C v N (eigQuot a Fil τ) hfQ
  have bF := Module.finBasisOfFinrankEq (Int0 v) (eigQuot a Fil τ) hrk
  have bLie := Module.finBasis (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))
  obtain ⟨bH⟩ := exists_basis_eigSub (ev a τ (cofac a τ)) hd hE6 hE7
  refine ⟨finrank (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)), ?_, ⟨bH⟩, ⟨bLie⟩, ⟨bF⟩, ?_⟩
  ·
    obtain ⟨n, b1, b1', -, -, -⟩ := hRL
    have hlift : ∀ i, ∃ z : Fin N → RS a, proj a Fil z = (bLie i : (Fin N → RS a) ⧸ Fil) :=
      fun i => Submodule.mkQ_surjective Fil _
    choose x hx using hlift
    obtain ⟨bL, -⟩ := exists_basis_comb hE4 hE8 hE10 bLie x hx bF
    obtain ⟨bHi, -⟩ := exists_basis_image hE6 bH
    have h1 := Fintype.card_congr (bL.indexEquiv b1)
    have h2 := Fintype.card_congr (bHi.indexEquiv b1')
    simp only [Fintype.card_sum, Fintype.card_fin] at h1 h2
    omega
  · intro h l x hx f e
    obtain ⟨c, hc, h1, h2⟩ := det_part hE4 hE6 hE8 hE9 hE10 hRL h l x hx f e
    exact ⟨c, hc.trans hr, h1, h2⟩

end GlobalTheory.HerbDet
