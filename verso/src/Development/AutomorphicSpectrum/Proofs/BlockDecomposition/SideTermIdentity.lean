import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic

noncomputable section

namespace GlobalTheory.CompanionTheory.MirSides

open Matrix PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
open GlobalTheory.CompanionTheory.CMMirror
open scoped NumberField.AdeleRing
open NumberField

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use extensionality with `r c`. Rewrite using `[tInv_coe]`. Use `show (Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]))ᵀ r c = Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) r c`. Rewrite using `[Matrix.diagonal_transpose]`.
-/
theorem tInv_dgl (d : ι → IdeleGroup k) : tInv (dgl d) = dgl fun i => (d i)⁻¹ := by
  ext r c
  rw [tInv_coe]
  show (Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]))ᵀ r c =
    Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) r c
  rw [Matrix.diagonal_transpose]

/- English proof (translation)
Take `⟨x, rfl⟩` from `h`. Conclude with `⟨tInv x, (tInv_map _ x).symm⟩`.
-/
theorem tInv_mem_ratGL {E R : Type} [Field E] [CommRing R] (A : Ad E R) (g : GL ι R) (h : g ∈ A.ratGL ι) :
    tInv g ∈ A.ratGL ι := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨tInv x, (tInv_map _ x).symm⟩

variable {G : Type} [Group G]

/- English proof (translation)
Unfold `kap`. Rewrite using `[MonoidHom.comp_apply, ← tInv_dgl, map_mul, map_mul, map_inv]`.
-/
theorem kap_tInv (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (g : G) :
    kap (tInv.comp π) (fun i => (d i)⁻¹) g = tInv (kap π d g) := by
  unfold kap
  rw [MonoidHom.comp_apply, ← tInv_dgl, map_mul, map_mul, map_inv]

/- English proof (translation)
Take `⟨κ', hκ', e⟩` from `h.piK κ hκ`. Establish `e' : π κ * dgl d = dgl d * κ'` using `Units.ext e`. Establish `: kap π d κ = κ'`. Unfold `kap`. Rewrite using `[mul_assoc, e', inv_mul_cancel_left]`.

Rewrite using `[this]`. Conclude with `hκ'`.
-/
theorem kap_mem [TopologicalSpace G] {π : G →* GL ι 𝔸[k]} {Γ K : Subgroup G} {i₀ i₁ : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η η' l : G → ℝ} (h : MirData π Γ K i₀ i₁ ω d c η η' l) (κ : G) (hκ : κ ∈ K) :
    kap π d κ ∈ (adStd k).kGL ι := by
  obtain ⟨κ', hκ', e⟩ := h.piK κ hκ
  have e' : π κ * dgl d = dgl d * κ' := Units.ext e
  have : kap π d κ = κ' := by
    unfold kap
    rw [mul_assoc, e', inv_mul_cancel_left]
  rw [this]
  exact hκ'

/- English proof (translation)
Establish `h1 : tInv p ∈ stab R ({i} : Set ι)` using `(tInv_mem_stab p {i}).2 hp`. Establish `h2 : tInv p⁻¹ ∈ stab R ({i} : Set ι)` using `(tInv_mem_stab p⁻¹ {i}).2 (inv_mem hp)`. Establish `e` using `hmul _ h1 _ h2`. Establish `b1 : bdet ({i} : Set ι) (1 : GL ι R) = 1`. Use `hmul 1 (one_mem _) 1 (one_mem _)` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Conclude with `left_eq_mul.1 this`. Rewrite `e` using `[← map_mul, mul_inv_cancel, map_one, b1, bdet_tInv {i} p⁻¹, inv_inv]`. Conclude with `eq_inv_of_mul_eq_one_left e.symm`.
-/
theorem bdet_tInv_of_mem {R : Type} [CommRing R] {i : ι}
    (hmul : ∀ p ∈ stab R ({i} : Set ι), ∀ q ∈ stab R ({i} : Set ι),
      bdet ({i} : Set ι) (p * q) = bdet {i} p * bdet {i} q)
    (p : GL ι R) (hp : p ∈ stab R ({i}ᶜ : Set ι)) : bdet ({i} : Set ι) (tInv p) = (bdet {i} p)⁻¹ := by
  have h1 : tInv p ∈ stab R ({i} : Set ι) := (tInv_mem_stab p {i}).2 hp
  have h2 : tInv p⁻¹ ∈ stab R ({i} : Set ι) := (tInv_mem_stab p⁻¹ {i}).2 (inv_mem hp)
  have e := hmul _ h1 _ h2
  have b1 : bdet ({i} : Set ι) (1 : GL ι R) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_mul.1 this
  rw [← map_mul, mul_inv_cancel, map_one, b1, bdet_tInv {i} p⁻¹, inv_inv] at e
  exact eq_inv_of_mul_eq_one_left e.symm

/- English proof (translation)
Establish `h1` using `h.lgmul 1 1`. Establish `h2` using `h.lgmul b b⁻¹`. Rewrite `h1` using `[mul_one]`. Rewrite `h2` using `[mul_inv_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lg_inv {A : Ad k 𝔸[k]} (h : A.GoodL) (b : (𝔸[k])ˣ) : A.lg b⁻¹ = - A.lg b := by
  have h1 := h.lgmul 1 1
  have h2 := h.lgmul b b⁻¹
  rw [mul_one] at h1
  rw [mul_inv_cancel] at h2
  linarith

/- English proof (translation)
Establish `e : ω.toIdele b * ω.toIdele b = 1`. Rewrite using `[HeckeCharacter.toIdele_apply]`. Conclude with `DFunLike.congr_fun h (IdeleClassGroup.mk k b)`. Rewrite using `[map_inv]`. Conclude with `inv_eq_of_mul_eq_one_right e`.
-/
theorem toIdele_inv {ω : HeckeCharacter k} (h : ω * ω = 1) (b : IdeleGroup k) :
    ω.toIdele b⁻¹ = ω.toIdele b := by
  have e : ω.toIdele b * ω.toIdele b = 1 := by
    rw [HeckeCharacter.toIdele_apply]
    exact DFunLike.congr_fun h (IdeleClassGroup.mk k b)
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_right e

/- English proof (translation)
Establish `hp : 0 < (IdeleGroup.ideleModule k x : ℝ)` using `(IdeleGroup.ideleModule k x).2`. Use `show _ = Complex.exp ((Real.log (IdeleGroup.ideleModule k x : ℝ) : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_exp, Real.exp_log hp, modPow, Complex.cpow_one]`.
-/
theorem modPow_one_eq (x : IdeleGroup k) :
    modPow x 1 = Complex.exp ((adStd k).lg x : ℝ) := by
  have hp : 0 < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  show _ = Complex.exp ((Real.log (IdeleGroup.ideleModule k x : ℝ) : ℝ) : ℂ)
  rw [← Complex.ofReal_exp, Real.exp_log hp, modPow, Complex.cpow_one]

/- English proof (translation)
Introduce `hS hB G _ _ _ _ K _ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l h`. Establish `hG` using `hS k`. Establish `hmul` using `(hB k 𝔸[k] (adStd k) hG ι {i₁}).2.1`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `{ two := h.two sq := h.sq cont := h.cont piK := kap_mem h piΓ := h.piΓ trans := h.trans _ (Or.inl rfl) mem := fun _ => Iff.rfl par := h.par ht := h.ht val := fun p hp => h.val p hp }`.

Use `{ two := h.two sq := h.sq cont := cont_tInv.comp h.cont piK := fun κ hκ => ?_ piΓ := fun γ hγ => tInv_mem_ratGL _ _ (h.piΓ γ hγ) trans := fun g hg => ?_ mem := fun g => (tInv_mem_stab (π g) {i₁}).symm par := h.par' ht := h.ht' val := fun p hp => ?_ }` and prove the remaining obligations. Rewrite using `[kap_tInv]`. Conclude with `tInv_mem_kGL _ _ (kap_mem h κ hκ)`. Take `⟨γ, hγ, e⟩` from `h.trans {i₁}ᶜ (Or.inr rfl) (tInv g) (tInv_mem_ratGL _ _ hg)`. Use `⟨γ, hγ, ?_⟩` and prove the remaining obligations.

Establish `e'` using `(tInv_mem_stab _ {i₁}).2 e`. Rewrite `e'` using `[map_mul, tInv_tInv, map_inv]`. Conclude with `e'`. Establish `hp' : π p ∈ stab 𝔸[k] ({i₁}ᶜ : Set ι)` using `hp`. Establish `hb` using `bdet_tInv_of_mem hmul (π p) hp'`.

Take `⟨v1, v2⟩` from `h.val' p hp'`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show c p = ω.toIdele (bdet {i₁} (tInv (π p)))`. Rewrite using `[hb, toIdele_inv h.sq]`. Conclude with `v1`.

Use `show η' p = (adStd k).lg (bdet {i₁} (tInv (π p)))`. Rewrite using `[hb, lg_inv hG]`. Conclude with `v2`. Introduce `g`. Rewrite using `[map_mul, tInv_dgl]`.

Both sides reduce to the same expression. Introduce `g`. Rewrite using `[map_mul, modPow_mul, modPow_one_eq (Matrix.GeneralLinearGroup.det (π g)), ← h.vall g]`.
-/
theorem sideOf : StdGood → BdetLaw → SideOf := by
  intro hS hB G _ _ _ _ K _ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l h
  have hG := hS k
  have hmul := (hB k 𝔸[k] (adStd k) hG ι {i₁}).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { two := h.two
        sq := h.sq
        cont := h.cont
        piK := kap_mem h
        piΓ := h.piΓ
        trans := h.trans _ (Or.inl rfl)
        mem := fun _ => Iff.rfl
        par := h.par
        ht := h.ht
        val := fun p hp => h.val p hp }
  · refine
      { two := h.two
        sq := h.sq
        cont := cont_tInv.comp h.cont
        piK := fun κ hκ => ?_
        piΓ := fun γ hγ => tInv_mem_ratGL _ _ (h.piΓ γ hγ)
        trans := fun g hg => ?_
        mem := fun g => (tInv_mem_stab (π g) {i₁}).symm
        par := h.par'
        ht := h.ht'
        val := fun p hp => ?_ }
    · rw [kap_tInv]
      exact tInv_mem_kGL _ _ (kap_mem h κ hκ)
    · obtain ⟨γ, hγ, e⟩ := h.trans {i₁}ᶜ (Or.inr rfl) (tInv g) (tInv_mem_ratGL _ _ hg)
      refine ⟨γ, hγ, ?_⟩
      have e' := (tInv_mem_stab _ {i₁}).2 e
      rw [map_mul, tInv_tInv, map_inv] at e'
      exact e'
    · have hp' : π p ∈ stab 𝔸[k] ({i₁}ᶜ : Set ι) := hp
      have hb := bdet_tInv_of_mem hmul (π p) hp'
      obtain ⟨v1, v2⟩ := h.val' p hp'
      refine ⟨?_, ?_⟩
      · show c p = ω.toIdele (bdet {i₁} (tInv (π p)))
        rw [hb, toIdele_inv h.sq]
        exact v1
      · show η' p = (adStd k).lg (bdet {i₁} (tInv (π p)))
        rw [hb, lg_inv hG]
        exact v2
  · intro g
    rw [map_mul, tInv_dgl]
    rfl
  · intro g
    rw [map_mul, modPow_mul, modPow_one_eq (Matrix.GeneralLinearGroup.det (π g)), ← h.vall g]

end GlobalTheory.CompanionTheory.MirSides
