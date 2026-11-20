import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairNumberRelabel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalDivisorJoinPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureBirational
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Blocks

variable (K : Type*)

def closureBlockEquiv : Option (Option K) ≃ K ⊕ Option Unit where
  toFun
    | none => Sum.inr none
    | some none => Sum.inr (some ())
    | some (some k) => Sum.inl k
  invFun
    | Sum.inl k => some (some k)
    | Sum.inr none => none
    | Sum.inr (some _) => some none
  left_inv := by rintro (_ | (_ | k)) <;> rfl
  right_inv := by rintro (k | (_ | ⟨⟩)) <;> rfl

variable {K} (ι : K → Type) (M M' : ℕ)

def closureVarEquiv :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) ≃ (Σ s, Sum.elim ι (lineBlocks M M') s) where
  toFun
    | ⟨none, l⟩ => ⟨Sum.inr none, l⟩
    | ⟨some none, l⟩ => ⟨Sum.inr (some ()), l⟩
    | ⟨some (some k), i⟩ => ⟨Sum.inl k, i⟩
  invFun
    | ⟨Sum.inl k, i⟩ => ⟨some (some k), i⟩
    | ⟨Sum.inr none, l⟩ => ⟨none, l⟩
    | ⟨Sum.inr (some _), l⟩ => ⟨some none, l⟩
  left_inv := by rintro ⟨_ | (_ | k), l⟩ <;> rfl
  right_inv := by rintro ⟨k | (_ | ⟨⟩), l⟩ <;> rfl

/- English proof (translation)
Apply the tactic sequence `rcases v with ⟨_ | (_ | k), l⟩ <;> rfl`.
-/
theorem closureVarEquiv_fst (v : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    (closureVarEquiv ι M M' v).1 = closureBlockEquiv K v.1 := by
  rcases v with ⟨_ | (_ | k), l⟩ <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `o`. Apply the tactic sequence `rcases o with _ | (_ | k) <;> rfl`.
-/
theorem joinDeg_comp_closureBlockEquiv (L : K → ℤ) :
    joinDeg (K' := Option Unit) L ∘ closureBlockEquiv K = liftPairDeg L := by
  funext o
  rcases o with _ | (_ | k) <;> rfl

/- English proof (translation)
Rewrite using `[liftPairForm, rename_rename]`. Both sides reduce to the same expression.
-/
theorem rename_liftPairForm {R : Type*} [CommRing R] (F : MRing ι R) :
    rename (closureVarEquiv ι M M') (liftPairForm M M' F) = joinForm (ι' := lineBlocks M M') F := by
  rw [liftPairForm, rename_rename]
  rfl

end Blocks

section Data

variable {K : Type} {ι : K → Type} {m : ℕ}

def joinClosureDeg (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) : Fin (1 + m) → K ⊕ Option Unit → ℤ :=
  Fin.append (fun _ : Fin 1 => ζ ∘ (closureBlockEquiv K).symm) (fun j => joinDeg (L j))

def joinClosureForm {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : Fin (1 + m) → MRing (Sum.elim ι (lineBlocks M M')) R :=
  Fin.append (fun _ : Fin 1 => h) (fun j => joinForm (F j))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun i => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [joinClosureDeg, closureDeg, Fin.append_left]`. Use function extensionality and compare the values at `o`. Simplify using the standard rewrite rules.

Simplify using `only [joinClosureDeg, closureDeg, Fin.append_right]`. Conclude with `joinDeg_comp_closureBlockEquiv _`.
-/
theorem joinClosureDeg_comp (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    (fun i => joinClosureDeg ζ L i ∘ closureBlockEquiv K) = closureDeg ζ L := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureDeg, closureDeg, Fin.append_left]
    funext o
    simp
  · simp only [joinClosureDeg, closureDeg, Fin.append_right]
    exact joinDeg_comp_closureBlockEquiv _

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[joinClosureDeg, Fin.append_right]`.
-/
theorem joinClosureDeg_natAdd (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    joinClosureDeg ζ L ∘ Fin.natAdd 1 = fun j => joinDeg (L j) := by
  funext j
  simp [joinClosureDeg, Fin.append_right]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun i => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [joinClosureForm, closureForm, Fin.append_left]`. Simplify using `only [joinClosureForm, closureForm, Fin.append_right]`. Conclude with `rename_liftPairForm ι M M' _`.
-/
theorem rename_closureForm {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (bundleIdx (bundleIdx ι M) M') R)
    (F : Fin m → MRing ι R) :
    (fun i => rename (closureVarEquiv ι M M') (closureForm M M' h F i)) =
      joinClosureForm M M' (rename (closureVarEquiv ι M M') h) F := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [joinClosureForm, closureForm, Fin.append_left]
  · simp only [joinClosureForm, closureForm, Fin.append_right]
    exact rename_liftPairForm ι M M' _

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[joinClosureForm, Fin.append_right]`.
-/
theorem joinClosureForm_natAdd {R : Type*} [CommRing R] (M M' : ℕ) (h : MRing (Sum.elim ι (lineBlocks M M')) R)
    (F : Fin m → MRing ι R) : joinClosureForm M M' h F ∘ Fin.natAdd 1 = fun j => joinForm (F j) := by
  funext j
  simp [joinClosureForm, Fin.append_right]

end Data

section PointIdeal

/- English proof (translation)
Establish `key : ∀ f, pointConeMap R y (rename σ f) = rename e (pointConeMap R (y ∘ σ) f)`. Introduce `f`. Establish `h : (pointConeMap R y).toRingHom.comp (rename σ).toRingHom = (rename e).toRingHom.comp (pointConeMap R (y ∘ σ)).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[pointConeMap, MvPolynomial.algebraMap_eq]`. Introduce `v`. Simplify using `[pointConeMap, hσ]`. Use `RingHom.congr_fun h f` as an intermediate fact. Simplify using `using this`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Rewrite using `[Ideal.mem_comap]`. Simplify using `only [pointIdeal, RingHom.mem_ker] at hf ⊢`.

Rewrite using `[key, hf, map_zero]`. Introduce `f hf`. Establish `hf' : rename σ (rename σ.symm f) = f`. Rewrite using `[rename_rename]`. Simplify using the standard rewrite rules.

Rewrite using `[← hf']`. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Simplify using `only [pointIdeal, RingHom.mem_ker] at hf ⊢`. Apply `rename_injective _ e.injective` to reduce the goal to its premises. Rewrite using `[map_zero, ← key, hf', hf]`.
-/
theorem pointIdeal_map_rename {K₁ K₂ : Type*} {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*} {R Φ : Type*} [CommRing R]
    [Field Φ] [Algebra R Φ] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Φ) : (pointIdeal R (y ∘ σ)).map (rename σ) = pointIdeal R y := by
  have key : ∀ f, pointConeMap R y (rename σ f) = rename e (pointConeMap R (y ∘ σ) f) := by
    intro f
    have h : (pointConeMap R y).toRingHom.comp (rename σ).toRingHom =
        (rename e).toRingHom.comp (pointConeMap R (y ∘ σ)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, MvPolynomial.algebraMap_eq]
      · intro v
        simp [pointConeMap, hσ]
    have := RingHom.congr_fun h f
    simpa using this
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    rw [key, hf, map_zero]
  · intro f hf
    have hf' : rename σ (rename σ.symm f) = f := by
      rw [rename_rename]
      simp
    rw [← hf']
    apply Ideal.mem_map_of_mem
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    apply rename_injective _ e.injective
    rw [map_zero, ← key, hf', hf]

/- English proof (translation)
Establish `key : ∀ f, pointConeMap O (fun p => algebraMap Ω Φ (y p)) f = MvPolynomial.map (algebraMap Ω Φ) (pointConeMap O y f)`. Introduce `f`. Establish `h : (pointConeMap O (fun p => algebraMap Ω Φ (y p))).toRingHom = (MvPolynomial.map (algebraMap Ω Φ)).comp (pointConeMap O y).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[pointConeMap, IsScalarTower.algebraMap_apply O Ω Φ]`. Introduce `v`. Simplify using `[pointConeMap]`. Use `RingHom.congr_fun h f` as an intermediate fact. Simplify using `using this`.

Use extensionality with `f`. Simplify using `only [pointIdeal, RingHom.mem_ker, key]`. Conclude with `⟨fun h => map_injective _ (algebraMap Ω Φ).injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩`.
-/
theorem pointIdeal_algebraMap {K : Type*} {ι : K → Type*} {O Ω Φ : Type*} [CommRing O] [Field Ω] [Field Φ]
    [Algebra O Ω] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ] (y : (Σ k, ι k) → Ω) :
    pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := by
  have key : ∀ f, pointConeMap O (fun p => algebraMap Ω Φ (y p)) f =
      MvPolynomial.map (algebraMap Ω Φ) (pointConeMap O y f) := by
    intro f
    have h : (pointConeMap O (fun p => algebraMap Ω Φ (y p))).toRingHom =
        (MvPolynomial.map (algebraMap Ω Φ)).comp (pointConeMap O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, IsScalarTower.algebraMap_apply O Ω Φ]
      · intro v
        simp [pointConeMap]
    have := RingHom.congr_fun h f
    simpa using this
  ext f
  simp only [pointIdeal, RingHom.mem_ker, key]
  exact ⟨fun h => map_injective _ (algebraMap Ω Φ).injective (by rw [h, map_zero]),
    fun h => by rw [h, map_zero]⟩

end PointIdeal

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hk1 hkN f₁ g₁ hD₁ _ n z z' fz gz hz r Bf hBf As Bs hAs hBs Q hQ`. Use `letI : ∀ s, Fintype (Sum.elim ι (lineBlocks M M') s) := fun s => match s with`. Consider the case `Sum.inl k => inferInstanceAs (Fintype (ι k))`. Consider the case `Sum.inr o => inferInstanceAs (Fintype (lineBlocks M M' o))`. Establish `hpt : joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k) ∘ closureVarEquiv ι M M' = flagClosurePt y w e φ φ' t k`.

Use function extensionality and compare the values at `p`. Apply the tactic sequence `rcases p with ⟨_ | (_ | o), l⟩ <;> rfl`. Establish `hPJ : (pointIdeal O (flagClosurePt y w e φ φ' t k)).map (rename (closureVarEquiv ι M M')) = pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k))`. Rewrite using `[← hpt]`. Conclude with `pointIdeal_map_rename (closureBlockEquiv K) _ (closureVarEquiv_fst ι M M') _`.

Establish `hPV : pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y` using `pointIdeal_algebraMap y`. Take `⟨hRmod, hRvert, hRnum⟩` from `hRel O ϖ (Option (Option K)) (bundleIdx (bundleIdx ι M) M') (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) (closureBlockEquiv K) (closureVarEquiv ι M M') (closureVarEquiv_fst ι M M') (pointIdeal O (flagClosurePt y w e φ φ' t k))`. Rewrite `hRmod`, `hRvert`, `hRnum` using `[hPJ]`. Establish `hJmod : IsModelOver (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k))) (d + (k - 1))` using `hRmod _ (hMod O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk1 hkN).1`. Establish `hvert : ∀ i, IsVerticalDivisor (pointIdeal O (fun p => algebraMap Ω Φ (y p))) ϖ (Fin.append x z i - Fin.append x' z' i) (Fin.append f fz i) (Fin.append g gz i)`.

Rewrite using `[hPV]`. Conclude with `fun i => Fin.addCases (fun i => by simpa only [Fin.append_left] using hF.vertical i) (fun j => by simpa only [Fin.append_right] using hz j) i`. Establish `hT` using `hRnum (1 + (N + n)) (joinClosureDeg (zetaFirst a₀) (Fin.append x z)) (joinClosureDeg (zetaSecond a₀') (Fin.append x' z')) (closureForm M M' f₁ (Fin.append f fz)) (closureForm M M' g₁ (Fin.append g gz)) As (Q.map joinDeg)`. Establish `hQ' : (Q.map joinDeg).map (· ∘ closureBlockEquiv K) = Q.map liftPairDeg`. Rewrite using `[List.map_map]`.

Conclude with `List.map_congr_left fun L _ => joinDeg_comp_closureBlockEquiv L`. Rewrite `hT` using `[rename_closureForm, rename_closureForm, joinClosureDeg_comp, joinClosureDeg_comp, hQ']`. Rewrite using `[← hT]`. Establish `hvJ : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k))) ϖ (joinClosureDeg (zetaFirst a₀) (Fin.append x z) i - joinClosureDeg (zetaSecond a₀') (Fin.append x' z') i) (joinClosureForm M M' (rename (closureVarEquiv ι M M') f₁ …`. Introduce `i`.

Use `Fin.addCases (fun i => ?_) (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [joinClosureDeg, joinClosureForm, Fin.append_left]`. Apply `hRvert` to reduce the goal to its premises. Establish `hζ : (zetaFirst a₀ ∘ (closureBlockEquiv K).symm - zetaSecond a₀' ∘ (closureBlockEquiv K).symm) ∘ closureBlockEquiv K = zetaFirst a₀ - zetaSecond a₀'`. Use function extensionality and compare the values at `o`.

Simplify using the standard rewrite rules. Rewrite using `[hζ]`. Conclude with `hD₁`. Simplify using `only [joinClosureDeg, joinClosureForm, Fin.append_right]`. Establish `hd : joinDeg (K'` using `Option Unit) (Fin.append x z j) - joinDeg (Fin.append x' z' j) = joinDeg (Fin.append x z j - Fin.append x' z' j) := by`.

Use function extensionality and compare the values at `s`. Apply the tactic sequence `rcases s with s | s <;> simp [joinDeg]`. Rewrite using `[hd]`. Conclude with `hVJ O ϖ Φ K ι (Option Unit) (lineBlocks M M') _ _ _ _ _ (hvert j)`. Rewrite using `[hExp O ϖ hϖ (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) _ (d + (k - 1)) hJmod (1 + (N + n)) _ _ _ _ hvJ r (rename (Fin.natAdd 1) Bf) (hBf.rename_isHomogeneous) As (pushExpansion (Fin.natAdd 1) Bs) hAs (isPairExpansion_push _ hBs) (Q.map joinDeg) (by rw [List.length_map]; om …`.

Establish `hPB` using `hPull O ϖ hϖ Φ K ι (Option Unit) (lineBlocks M M') (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k) d (k - 1) (by rw [hPV]; exact hV) hJmod (N + n) (Fin.append x z) (Fin.append x' z') (Fin.append f fz) (Fin.append g gz) hvert r Bf hBf Bs hBs Q (by omega)`. Use `split_ifs with hk`. Take `rfl` from `hk`. Rewrite using `[hPB.2 (hBir O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht hkN), hPV]`. Conclude with `hPB.1 (by omega)`.
-/
theorem SegreFlagClosurePullback.proof (hPull : PairNumberPullback.Statement)
    (hExp : PairNumberExpansionIndependence.Statement) (hMod : SegreFlagClosureModel.Statement)
    (hRel : PairNumberRelabel.Statement) (hVJ : VerticalDivisorJoinPullback.Statement)
    (hBir : SegreFlagClosureBirational.Statement) : SegreFlagClosurePullback.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ'
    hφ hφ' Φ _ _ _ _ e t ht k hk1 hkN f₁ g₁ hD₁ _ n z z' fz gz hz r Bf hBf As Bs hAs hBs Q hQ
  classical
  letI : ∀ s, Fintype (Sum.elim ι (lineBlocks M M') s) := fun s =>
    match s with
    | Sum.inl k => inferInstanceAs (Fintype (ι k))
    | Sum.inr o => inferInstanceAs (Fintype (lineBlocks M M' o))

  have hpt : joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k) ∘ closureVarEquiv ι M M' =
      flagClosurePt y w e φ φ' t k := by
    funext p
    rcases p with ⟨_ | (_ | o), l⟩ <;> rfl
  have hPJ : (pointIdeal O (flagClosurePt y w e φ φ' t k)).map (rename (closureVarEquiv ι M M')) =
      pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k)) := by
    rw [← hpt]
    exact pointIdeal_map_rename (closureBlockEquiv K) _ (closureVarEquiv_fst ι M M') _
  have hPV : pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := pointIdeal_algebraMap y
  obtain ⟨hRmod, hRvert, hRnum⟩ := hRel O ϖ (Option (Option K)) (bundleIdx (bundleIdx ι M) M')
    (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) (closureBlockEquiv K) (closureVarEquiv ι M M')
    (closureVarEquiv_fst ι M M') (pointIdeal O (flagClosurePt y w e φ φ' t k))
  rw [hPJ] at hRmod hRvert hRnum
  have hJmod : IsModelOver (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) (d + (k - 1)) :=
    hRmod _ (hMod O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k
      hk1 hkN).1

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O (fun p => algebraMap Ω Φ (y p))) ϖ
      (Fin.append x z i - Fin.append x' z' i) (Fin.append f fz i) (Fin.append g gz i) := by
    rw [hPV]
    exact fun i => Fin.addCases (fun i => by simpa only [Fin.append_left] using hF.vertical i)
      (fun j => by simpa only [Fin.append_right] using hz j) i

  have hT := hRnum (1 + (N + n)) (joinClosureDeg (zetaFirst a₀) (Fin.append x z))
    (joinClosureDeg (zetaSecond a₀') (Fin.append x' z')) (closureForm M M' f₁ (Fin.append f fz))
    (closureForm M M' g₁ (Fin.append g gz)) As (Q.map joinDeg)
  have hQ' : (Q.map joinDeg).map (· ∘ closureBlockEquiv K) = Q.map liftPairDeg := by
    rw [List.map_map]
    exact List.map_congr_left fun L _ => joinDeg_comp_closureBlockEquiv L
  rw [rename_closureForm, rename_closureForm, joinClosureDeg_comp, joinClosureDeg_comp, hQ'] at hT
  rw [← hT]

  have hvJ : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) ϖ
      (joinClosureDeg (zetaFirst a₀) (Fin.append x z) i - joinClosureDeg (zetaSecond a₀') (Fin.append x' z') i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') f₁) (Fin.append f fz) i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') g₁) (Fin.append g gz) i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_left]
      apply hRvert
      have hζ : (zetaFirst a₀ ∘ (closureBlockEquiv K).symm - zetaSecond a₀' ∘ (closureBlockEquiv K).symm) ∘
          closureBlockEquiv K = zetaFirst a₀ - zetaSecond a₀' := by
        funext o
        simp
      rw [hζ]
      exact hD₁
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_right]
      have hd : joinDeg (K' := Option Unit) (Fin.append x z j) - joinDeg (Fin.append x' z' j) =
          joinDeg (Fin.append x z j - Fin.append x' z' j) := by
        funext s
        rcases s with s | s <;> simp [joinDeg]
      rw [hd]
      exact hVJ O ϖ Φ K ι (Option Unit) (lineBlocks M M') _ _ _ _ _ (hvert j)

  rw [hExp O ϖ hϖ (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) _ (d + (k - 1)) hJmod (1 + (N + n)) _ _ _ _
    hvJ r (rename (Fin.natAdd 1) Bf) (hBf.rename_isHomogeneous) As (pushExpansion (Fin.natAdd 1) Bs) hAs
    (isPairExpansion_push _ hBs) (Q.map joinDeg) (by rw [List.length_map]; omega),
    pairNum_pushExpansion, joinClosureDeg_natAdd, joinClosureDeg_natAdd, joinClosureForm_natAdd,
    joinClosureForm_natAdd]

  have hPB := hPull O ϖ hϖ Φ K ι (Option Unit) (lineBlocks M M') (fun p => algebraMap Ω Φ (y p))
    (flagLinePt w e φ φ' t k) d (k - 1) (by rw [hPV]; exact hV) hJmod (N + n) (Fin.append x z)
    (Fin.append x' z') (Fin.append f fz) (Fin.append g gz) hvert r Bf hBf Bs hBs Q (by omega)
  split_ifs with hk
  · obtain rfl := hk
    rw [hPB.2 (hBir O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht hkN),
      hPV]
  · exact hPB.1 (by omega)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
