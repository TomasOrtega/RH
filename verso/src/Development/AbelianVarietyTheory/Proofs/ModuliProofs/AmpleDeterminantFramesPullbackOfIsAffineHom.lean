import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFibreIso

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpPull

open GlobalTheory.LN GlobalTheory.ArcPull

/- English proof (translation)
Rewrite using `[← gs_pull r g z U h, gs_stalkMap r z (g ⁻¹ᵁ U) h, gs_pull (𝟙 Y) g (r z) U h, Category.id_comp]`.
-/
theorem gs_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z (g ⁻¹ᵁ U) h, gs_pull (𝟙 Y) g (r z) U h, Category.id_comp]

/- English proof (translation)
Rewrite using `[← Over.comp_left, whiskerRight_snd]`.
-/
theorem whisker_snd {Z : Scheme.{0}} (G : Over Z) {T T' : Over Z} (h : T' ⟶ T) :
    (h ▷ G).left ≫ (snd T G).left = (snd T' G).left := by
  rw [← Over.comp_left, whiskerRight_snd]

/- English proof (translation)
Rewrite using `[← Over.comp_left, whiskerRight_fst, Over.comp_left]`.
-/
theorem whisker_fst {Z : Scheme.{0}} (G : Over Z) {T T' : Over Z} (h : T' ⟶ T) :
    (h ▷ G).left ≫ (fst T G).left = (fst T' G).left ≫ h.left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

abbrev sv {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ} {T : Over Z} (s : LB.Sec (LPow G L (N : ℤ) T))
    {Y : Scheme.{0}} (r : Y ⟶ (T ⊗ G).left) (y : Y) (J : (Y ⟶ G.left) → L.ι) : Y.presheaf.stalk y :=
  sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) s r y J

/- English proof (translation)
Take `⟨J₀, hJ₀, e⟩` from `exists_good L hL (r y) (fun _ : Fin 1 => (snd T' G).left) (fun _ => J (r ≫ (snd T' G).left)) (fun _ _ _ => rfl) (fun _ => hJ (r ≫ (snd T' G).left))`. Establish `e₀` using `e 0`. Establish `H₀` using `congrArg (r.stalkMap y).hom (H (r y) J₀ hJ₀)`. Rewrite `H₀` using `[sval_of s _ _ J₀ (fun _ => J (r ≫ (snd T' G).left)) (fun _ => by rw [Category.id_comp]; exact e₀), map_sum]`. Establish `m : r y ∈ LB.wchart L (fun _ : Fin 1 => (snd T' G).left) (fun _ => J (r ≫ (snd T' G).left))` using `hJ.mem (fun _ : Fin 1 => (snd T' G).left) r`.

Use `(gs_stalkMap r y _ m _).trans (H₀.trans (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[map_mul, ← gs_stalk r _ y ⊤ trivial, sval_of (b i) _ _ J₀ (fun _ => J (r ≫ (snd T' G).left)) (fun _ => by rw [whisker_snd]; exact e₀), sv, sval_of (b i) (r ≫ (h ▷ G).left) y J (fun _ => J (r ≫ (snd T' G).left)) (fun _ => by rw [Category.assoc, whisker_snd])]`. Use `congrArg _ (gs_stalk r (h ▷ G).left y _ (Set.mem_iInter.2 fun _ => ?_) _).symm` and prove the remaining obligations. Use `show ((h ▷ G).left ≫ (snd T G).left) (r y) ∈ L.U (J (r ≫ (snd T' G).left))`. Rewrite using `[whisker_snd]`.

Conclude with `hJ (r ≫ (snd T' G).left)`.
-/
theorem lin_gen {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} (hL : L.IsLB) {N : ℕ} {T T' : Over Z} {h : T' ⟶ T} {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {c : Fin n → Γ(T'.left, ⊤)} {s : LB.Sec (LPow G L (N : ℤ) T')}
    (H : Lin G L N h b c s) {Y : Scheme.{0}} (r : Y ⟶ (T' ⊗ G).left) (y : Y) (J) (hJ : Good L y J) :
    sv s r y J = ∑ i, gs (r ≫ (fst T' G).left) y ⊤ (c i) * sv (b i) (r ≫ (h ▷ G).left) y J := by
  obtain ⟨J₀, hJ₀, e⟩ := exists_good L hL (r y) (fun _ : Fin 1 => (snd T' G).left) (fun _ => J (r ≫ (snd T' G).left))
    (fun _ _ _ => rfl) (fun _ => hJ (r ≫ (snd T' G).left))
  have e₀ := e 0
  have H₀ := congrArg (r.stalkMap y).hom (H (r y) J₀ hJ₀)
  rw [sval_of s _ _ J₀ (fun _ => J (r ≫ (snd T' G).left)) (fun _ => by rw [Category.id_comp]; exact e₀), map_sum] at H₀
  have m : r y ∈ LB.wchart L (fun _ : Fin 1 => (snd T' G).left) (fun _ => J (r ≫ (snd T' G).left)) :=
    hJ.mem (fun _ : Fin 1 => (snd T' G).left) r
  refine (gs_stalkMap r y _ m _).trans (H₀.trans (Finset.sum_congr rfl fun i _ => ?_))
  rw [map_mul, ← gs_stalk r _ y ⊤ trivial, sval_of (b i) _ _ J₀ (fun _ => J (r ≫ (snd T' G).left))
    (fun _ => by rw [whisker_snd]; exact e₀), sv, sval_of (b i) (r ≫ (h ▷ G).left) y J (fun _ => J (r ≫ (snd T' G).left))
    (fun _ => by rw [Category.assoc, whisker_snd])]
  refine congrArg _ (gs_stalk r (h ▷ G).left y _ (Set.mem_iInter.2 fun _ => ?_) _).symm
  show ((h ▷ G).left ≫ (snd T G).left) (r y) ∈ L.U (J (r ≫ (snd T' G).left))
  rw [whisker_snd]
  exact hJ (r ≫ (snd T' G).left)

variable {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {L : LB G.left} {L' : LB G'.left} {f : Z' ⟶ Z}
  {φ : G'.left ⟶ G.left}

def kap (hw : φ ≫ G.hom = G'.hom ≫ f) (T' : Over Z') (T : Over Z) (e : T'.left ⟶ T.left) (he : e ≫ T.hom = T'.hom ≫ f) :
    (T' ⊗ G').left ⟶ (T ⊗ G).left :=
  pullback.map T'.hom G'.hom T.hom G.hom e φ f he.symm hw.symm

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem kap_fst (hw : φ ≫ G.hom = G'.hom ≫ f) (T' : Over Z') (T : Over Z) (e : T'.left ⟶ T.left)
    (he : e ≫ T.hom = T'.hom ≫ f) : kap hw T' T e he ≫ (fst T G).left = (fst T' G').left ≫ e :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem kap_snd (hw : φ ≫ G.hom = G'.hom ≫ f) (T' : Over Z') (T : Over Z) (e : T'.left ⟶ T.left)
    (he : e ≫ T.hom = T'.hom ≫ f) : kap hw T' T e he ≫ (snd T G).left = (snd T' G').left ≫ φ :=
  pullback.lift_snd _ _ _

/- English proof (translation)
The claim follows from `pullback.hom_ext h₁ h₂`.
-/
theorem tens_ext {T : Over Z} {Y : Scheme.{0}} {a b : Y ⟶ (T ⊗ G).left} (h₁ : a ≫ (fst T G).left = b ≫ (fst T G).left)
    (h₂ : a ≫ (snd T G).left = b ≫ (snd T G).left) : a = b := pullback.hom_ext h₁ h₂

/- English proof (translation)
Use `tens_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, kap_fst, ← Category.assoc, whisker_fst, Category.assoc, hs, Category.assoc, whisker_fst, ← Category.assoc, ← Category.assoc, kap_fst]`. Rewrite using `[Category.assoc, kap_snd, ← Category.assoc, whisker_snd, Category.assoc, whisker_snd, kap_snd]`.
-/
theorem kap_sq (hw : φ ≫ G.hom = G'.hom ≫ f) {T₁' T₂' : Over Z'} {T₁ T₂ : Over Z} {e₁ : T₁'.left ⟶ T₁.left}
    (he₁ : e₁ ≫ T₁.hom = T₁'.hom ≫ f) {e₂ : T₂'.left ⟶ T₂.left} (he₂ : e₂ ≫ T₂.hom = T₂'.hom ≫ f)
    (h' : T₁' ⟶ T₂') (h : T₁ ⟶ T₂) (hs : h'.left ≫ e₂ = e₁ ≫ h.left) :
    (h' ▷ G').left ≫ kap hw T₂' T₂ e₂ he₂ = kap hw T₁' T₁ e₁ he₁ ≫ (h ▷ G).left := by
  refine tens_ext ?_ ?_
  · rw [Category.assoc, kap_fst, ← Category.assoc, whisker_fst, Category.assoc, hs, Category.assoc, whisker_fst,
      ← Category.assoc, ← Category.assoc, kap_fst]
  · rw [Category.assoc, kap_snd, ← Category.assoc, whisker_snd, Category.assoc, whisker_snd, kap_snd]

/- English proof (translation)
Establish `c : (snd (Over.mk a) G).left ≫ G.hom = ((fst (Over.mk a) G).left ≫ a') ≫ f`. Rewrite using `[Category.assoc, ← he, Category.id_comp]`. Conclude with `pullback.condition.symm`. Set `κ' : (Over.mk a ⊗ G).left ⟶ (Over.mk a' ⊗ G').left` to `pullback.lift (fst (Over.mk a) G).left (hP.lift _ _ c) (hP.lift_snd _ _ c).symm`. Establish `k₁ : κ' ≫ (fst (Over.mk a') G').left = (fst (Over.mk a) G).left` using `pullback.lift_fst _ _ _`.

Establish `k₂ : κ' ≫ (snd (Over.mk a') G').left = hP.lift _ _ c` using `pullback.lift_snd _ _ _`. Use `⟨κ', tens_ext ?_ ?_, tens_ext ?_ (hP.hom_ext ?_ ?_)⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, kap_fst, ← Category.assoc, k₁, Category.id_comp]`. Conclude with `Category.comp_id _`. Rewrite using `[Category.assoc, kap_snd, ← Category.assoc, k₂, Category.id_comp, hP.lift_fst]`.

Rewrite using `[Category.assoc, k₁, kap_fst, Category.id_comp]`. Conclude with `Category.comp_id _`. Rewrite using `[Category.assoc, Category.assoc, ← Category.assoc κ', k₂, hP.lift_fst, kap_snd, Category.id_comp]`. Rewrite using `[Category.assoc, Category.assoc, ← Category.assoc κ', k₂, hP.lift_snd, ← Category.assoc, kap_fst, Category.id_comp]`. Conclude with `(congrArg (· ≫ a') (Category.comp_id _)).trans pullback.condition`.
-/
theorem exists_kap_inv (hP : IsPullback φ G'.hom G.hom f) {Y : Scheme.{0}} (a' : Y ⟶ Z') (a : Y ⟶ Z)
    (he : 𝟙 Y ≫ a = a' ≫ f) : ∃ κ' : (Over.mk a ⊗ G).left ⟶ (Over.mk a' ⊗ G').left,
      κ' ≫ kap hP.w (Over.mk a') (Over.mk a) (𝟙 Y) he = 𝟙 _ ∧ kap hP.w (Over.mk a') (Over.mk a) (𝟙 Y) he ≫ κ' = 𝟙 _ := by
  have c : (snd (Over.mk a) G).left ≫ G.hom = ((fst (Over.mk a) G).left ≫ a') ≫ f := by
    rw [Category.assoc, ← he, Category.id_comp]; exact pullback.condition.symm
  let κ' : (Over.mk a ⊗ G).left ⟶ (Over.mk a' ⊗ G').left :=
    pullback.lift (fst (Over.mk a) G).left (hP.lift _ _ c) (hP.lift_snd _ _ c).symm
  have k₁ : κ' ≫ (fst (Over.mk a') G').left = (fst (Over.mk a) G).left := pullback.lift_fst _ _ _
  have k₂ : κ' ≫ (snd (Over.mk a') G').left = hP.lift _ _ c := pullback.lift_snd _ _ _
  refine ⟨κ', tens_ext ?_ ?_, tens_ext ?_ (hP.hom_ext ?_ ?_)⟩
  · rw [Category.assoc, kap_fst, ← Category.assoc, k₁, Category.id_comp]; exact Category.comp_id _
  · rw [Category.assoc, kap_snd, ← Category.assoc, k₂, Category.id_comp, hP.lift_fst]
  · rw [Category.assoc, k₁, kap_fst, Category.id_comp]; exact Category.comp_id _
  · rw [Category.assoc, Category.assoc, ← Category.assoc κ', k₂, hP.lift_fst, kap_snd, Category.id_comp]
  · rw [Category.assoc, Category.assoc, ← Category.assoc κ', k₂, hP.lift_snd, ← Category.assoc, kap_fst,
      Category.id_comp]
    exact (congrArg (· ≫ a') (Category.comp_id _)).trans pullback.condition

def Rel (w : LB.Iso L' (L.pull φ)) {N : ℕ} {T' : Over Z'} {T : Over Z} (κ : (T' ⊗ G').left ⟶ (T ⊗ G).left)
    (s : LB.Sec (LPow G L (N : ℤ) T)) (s' : LB.Sec (LPow G' L' (N : ℤ) T')) : Prop :=
  ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G').left) (y : Y) J J', Good L y J → Good L' y J' →
    sv s (r ≫ κ) y J = (om w y J J' (r ≫ (snd T' G').left) ^ (N : ℤ)).val * sv s' r y J'

variable {w : LB.Iso L' (L.pull φ)}

/- English proof (translation)
Take `⟨a, ha, -⟩` from `SecPull.existsUnique_secPull _ _ _ _ L L' φ hL hL' w ((isGen_iff w).2 hw) (Fin 1) (fun _ => (snd T' G').left) (fun _ => (snd T G).left) (fun _ => (N : ℤ)) κ (fun _ => hκ.symm) s`. Use `⟨a, fun Y r y J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Use `ha Y r y (fun _ => J ((r ≫ (snd T' G').left) ≫ φ)) (fun _ => J' (r ≫ (snd T' G').left)) (fun _ => hJ ((r ≫ (snd T' G').left) ≫ φ)) (fun _ => hJ' (r ≫ (snd T' G').left))` as an intermediate fact. Rewrite `this` using `[Fin.prod_univ_one]`. Conclude with `(sval_of s (r ≫ κ) y J _ (fun _ => by rw [Category.assoc, hκ, Category.assoc])).trans this`.
-/
theorem exists_rel_down (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {N : ℕ} {T' : Over Z'} {T : Over Z}
    (κ : (T' ⊗ G').left ⟶ (T ⊗ G).left) (hκ : κ ≫ (snd T G).left = (snd T' G').left ≫ φ)
    (s : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s', Rel w κ s s' := by
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ L L' φ hL hL' w ((isGen_iff w).2 hw) (Fin 1)
    (fun _ => (snd T' G').left) (fun _ => (snd T G).left) (fun _ => (N : ℤ)) κ (fun _ => hκ.symm) s
  refine ⟨a, fun Y r y J J' hJ hJ' => ?_⟩
  have := ha Y r y (fun _ => J ((r ≫ (snd T' G').left) ≫ φ)) (fun _ => J' (r ≫ (snd T' G').left))
    (fun _ => hJ ((r ≫ (snd T' G').left) ≫ φ)) (fun _ => hJ' (r ≫ (snd T' G').left))
  rw [Fin.prod_univ_one] at this
  exact (sval_of s (r ≫ κ) y J _ (fun _ => by rw [Category.assoc, hκ, Category.assoc])).trans this

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_up_sec hw hL hL' (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T G).left) (fun _ => (N : ℤ)) κ' (fun _ => by rw [Category.assoc, ← hκ, ← Category.assoc, h₁, Category.id_comp]) s'`. Use `⟨a, fun Y r y J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Use `ha Y (r ≫ κ) y J J' hJ hJ'` as an intermediate fact. Rewrite `this` using `[Fin.prod_univ_one, Category.assoc r κ κ', h₂, Category.comp_id]`. Conclude with `this`.
-/
theorem exists_rel_up (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {N : ℕ} {T' : Over Z'} {T : Over Z}
    (κ : (T' ⊗ G').left ⟶ (T ⊗ G).left) (hκ : κ ≫ (snd T G).left = (snd T' G').left ≫ φ)
    (κ' : (T ⊗ G).left ⟶ (T' ⊗ G').left) (h₁ : κ' ≫ κ = 𝟙 _) (h₂ : κ ≫ κ' = 𝟙 _)
    (s' : LB.Sec (LPow G' L' (N : ℤ) T')) : ∃ s, Rel w κ s s' := by
  obtain ⟨a, ha⟩ := exists_up_sec hw hL hL' (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T G).left)
    (fun _ => (N : ℤ)) κ' (fun _ => by rw [Category.assoc, ← hκ, ← Category.assoc, h₁, Category.id_comp]) s'
  refine ⟨a, fun Y r y J J' hJ hJ' => ?_⟩
  have := ha Y (r ≫ κ) y J J' hJ hJ'
  rw [Fin.prod_univ_one, Category.assoc r κ κ', h₂, Category.comp_id] at this
  exact this

/- English proof (translation)
Establish `e : ∀ i, c i * sv (b i) ((r ≫ κ₁) ≫ (h ▷ G).left) y J = (om w y J J' (r ≫ (snd T₁' G').left) ^ (N : ℤ)).val * (c i * sv (b' i) (r ≫ (h' ▷ G').left) y J')` using `fun i => by`. Rewrite using `[Category.assoc, ← hs, ← Category.assoc, Rb i Y _ y J J' hJ hJ', Category.assoc, whisker_snd, mul_left_comm]`. Rewrite using `[R Y r y J J' hJ hJ', Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum, Units.mul_right_inj]`.
-/
theorem lin_pt_iff {N n : ℕ} {T₁' T₂' : Over Z'} {T₁ T₂ : Over Z} {κ₁ : (T₁' ⊗ G').left ⟶ (T₁ ⊗ G).left}
    {κ₂ : (T₂' ⊗ G').left ⟶ (T₂ ⊗ G).left} {h' : T₁' ⟶ T₂'} {h : T₁ ⟶ T₂}
    (hs : (h' ▷ G').left ≫ κ₂ = κ₁ ≫ (h ▷ G).left) {s : LB.Sec (LPow G L (N : ℤ) T₁)} {s'} (R : Rel w κ₁ s s')
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {b' : Fin n → LB.Sec (LPow G' L' (N : ℤ) T₂')}
    (Rb : ∀ i, Rel w κ₂ (b i) (b' i)) {Y : Scheme.{0}} (r : Y ⟶ (T₁' ⊗ G').left) (y : Y) {J J'} (hJ : Good L y J) (hJ' : Good L' y J')
    (c : Fin n → Y.presheaf.stalk y) :
    (sv s (r ≫ κ₁) y J = ∑ i, c i * sv (b i) ((r ≫ κ₁) ≫ (h ▷ G).left) y J) ↔
      sv s' r y J' = ∑ i, c i * sv (b' i) (r ≫ (h' ▷ G').left) y J' := by
  have e : ∀ i, c i * sv (b i) ((r ≫ κ₁) ≫ (h ▷ G).left) y J =
      (om w y J J' (r ≫ (snd T₁' G').left) ^ (N : ℤ)).val * (c i * sv (b' i) (r ≫ (h' ▷ G').left) y J') := fun i => by
    rw [Category.assoc, ← hs, ← Category.assoc, Rb i Y _ y J J' hJ hJ', Category.assoc, whisker_snd, mul_left_comm]
  rw [R Y r y J J' hJ hJ', Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum, Units.mul_right_inj]

/- English proof (translation)
Use `choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y)`. Conclude with `⟨I, hI⟩`.
-/
theorem good_ex {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (y : Y) : ∃ J, Good M y J := by
  choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y)
  exact ⟨I, hI⟩

/- English proof (translation)
Introduce `y J' hJ'`. Take `⟨J, hJ⟩` from `good_ex hL y`. Use `(lin_pt_iff hs R Rb (𝟙 _) y hJ hJ' _).1 (lin_gen hL H (𝟙 _ ≫ κ₁) y J hJ)` as an intermediate fact. Use `this.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Category.id_comp, Category.id_comp, he, ← gs_pull _ e y ⊤ trivial]`.

Both sides reduce to the same expression.
-/
theorem lin_down (hL : L.IsLB) {N n : ℕ} {T₁' T₂' : Over Z'} {T₁ T₂ : Over Z} {κ₁ : (T₁' ⊗ G').left ⟶ (T₁ ⊗ G).left}
    {κ₂ : (T₂' ⊗ G').left ⟶ (T₂ ⊗ G).left} {h' : T₁' ⟶ T₂'} {h : T₁ ⟶ T₂}
    (hs : (h' ▷ G').left ≫ κ₂ = κ₁ ≫ (h ▷ G).left) {e : T₁'.left ⟶ T₁.left}
    (he : κ₁ ≫ (fst T₁ G).left = (fst T₁' G').left ≫ e) {s : LB.Sec (LPow G L (N : ℤ) T₁)} {s'} (R : Rel w κ₁ s s')
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {b'} (Rb : ∀ i, Rel w κ₂ (b i) (b' i)) {c}
    (H : Lin G L N h b c s) : Lin G' L' N h' b' (fun i => e.appTop.hom (c i)) s' := by
  intro y J' hJ'
  obtain ⟨J, hJ⟩ := good_ex hL y
  have := (lin_pt_iff hs R Rb (𝟙 _) y hJ hJ' _).1 (lin_gen hL H (𝟙 _ ≫ κ₁) y J hJ)
  refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [Category.id_comp, Category.id_comp, he, ← gs_pull _ e y ⊤ trivial]
  rfl

/- English proof (translation)
Introduce `y J hJ`. Take `⟨J', hJ'⟩` from `good_ex hL' y`. Use `(lin_pt_iff hs R Rb κ' y hJ hJ' _).2 (lin_gen hL' H κ' y J' hJ')` as an intermediate fact. Rewrite `this` using `[hκ, Category.id_comp]`. Use `this.trans (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)` and prove the remaining obligations.

Use `(gs_pull (κ' ≫ (fst T₁' G').left) e y ⊤ trivial _).trans ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, ← he, ← Category.assoc, hκ, Category.id_comp]`.
-/
theorem lin_up (hL' : L'.IsLB) {N n : ℕ} {T₁' T₂' : Over Z'} {T₁ T₂ : Over Z} {κ₁ : (T₁' ⊗ G').left ⟶ (T₁ ⊗ G).left}
    {κ₂ : (T₂' ⊗ G').left ⟶ (T₂ ⊗ G).left} {h' : T₁' ⟶ T₂'} {h : T₁ ⟶ T₂}
    (hs : (h' ▷ G').left ≫ κ₂ = κ₁ ≫ (h ▷ G).left) {e : T₁'.left ⟶ T₁.left}
    (he : κ₁ ≫ (fst T₁ G).left = (fst T₁' G').left ≫ e) {κ' : (T₁ ⊗ G).left ⟶ (T₁' ⊗ G').left} (hκ : κ' ≫ κ₁ = 𝟙 _)
    {s : LB.Sec (LPow G L (N : ℤ) T₁)} {s'} (R : Rel w κ₁ s s')
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T₂)} {b'} (Rb : ∀ i, Rel w κ₂ (b i) (b' i)) {c : Fin n → Γ(T₁.left, ⊤)}
    (H : Lin G' L' N h' b' (fun i => e.appTop.hom (c i)) s') : Lin G L N h b c s := by
  intro y J hJ
  obtain ⟨J', hJ'⟩ := good_ex hL' y
  have := (lin_pt_iff hs R Rb κ' y hJ hJ' _).2 (lin_gen hL' H κ' y J' hJ')
  rw [hκ, Category.id_comp] at this
  refine this.trans (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
  refine (gs_pull (κ' ≫ (fst T₁' G').left) e y ⊤ trivial _).trans ?_
  rw [Category.assoc, ← he, ← Category.assoc, hκ, Category.id_comp]

/- English proof (translation)
Introduce `s'`. Establish `h₁ : 𝟙 Y ≫ (χ ≫ e) ≫ T.hom = (χ ≫ T'.hom) ≫ f` using `by rw [Category.id_comp, Category.assoc, he, Category.assoc]`. Take `⟨κ', k₁, k₂⟩` from `exists_kap_inv hP _ _ h₁`. Take `⟨s, R⟩` from `exists_rel_up hw hL hL' _ (kap_snd _ _ _ _ _) κ' k₁ k₂ s'`. Establish `hs` using `kap_sq hP.w (T₁' := Over.mk (χ ≫ T'.hom)) (T₁ := Over.mk ((χ ≫ e) ≫ T.hom)) (e₁ := 𝟙 Y) h₁ he (Over.homMk χ rfl) (Over.homMk (χ ≫ e) rfl) (Category.id_comp _).symm`.

Take `⟨c, hc, hu⟩` from `H s`. Conclude with `⟨c, lin_down hL hs (kap_fst _ _ _ _ _) R Rb hc, fun c' hc' => hu c' (lin_up hL' hs (kap_fst _ _ _ _ _) k₁ R Rb hc')⟩`.
-/
theorem basis_down (hP : IsPullback φ G'.hom G.hom f) (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {N n : ℕ}
    {T' : Over Z'} {T : Over Z} {e : T'.left ⟶ T.left} (he : e ≫ T.hom = T'.hom ≫ f) {Y : Scheme.{0}} (χ : Y ⟶ T'.left)
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {b'} (Rb : ∀ i, Rel w (kap hP.w T' T e he) (b i) (b' i))
    (H : BasisAlong G L N (Over.homMk (χ ≫ e) rfl : Over.mk ((χ ≫ e) ≫ T.hom) ⟶ T) b) :
    BasisAlong G' L' N (Over.homMk χ rfl : Over.mk (χ ≫ T'.hom) ⟶ T') b' := by
  intro s'
  have h₁ : 𝟙 Y ≫ (χ ≫ e) ≫ T.hom = (χ ≫ T'.hom) ≫ f := by rw [Category.id_comp, Category.assoc, he, Category.assoc]
  obtain ⟨κ', k₁, k₂⟩ := exists_kap_inv hP _ _ h₁
  obtain ⟨s, R⟩ := exists_rel_up hw hL hL' _ (kap_snd _ _ _ _ _) κ' k₁ k₂ s'
  have hs := kap_sq hP.w (T₁' := Over.mk (χ ≫ T'.hom)) (T₁ := Over.mk ((χ ≫ e) ≫ T.hom)) (e₁ := 𝟙 Y) h₁ he
    (Over.homMk χ rfl) (Over.homMk (χ ≫ e) rfl) (Category.id_comp _).symm
  obtain ⟨c, hc, hu⟩ := H s
  exact ⟨c, lin_down hL hs (kap_fst _ _ _ _ _) R Rb hc, fun c' hc' =>
    hu c' (lin_up hL' hs (kap_fst _ _ _ _ _) k₁ R Rb hc')⟩

/- English proof (translation)
Rewrite using `[← cancel_mono U.ι]`. Simplify using the standard rewrite rules.
-/
theorem res_sq {U V : Z.Opens} {U' V' : Z'.Opens} (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V) (h : V ≤ U) (h' : V' ≤ U') :
    Z'.homOfLE h' ≫ f.resLE U U' hU = f.resLE V V' hV ≫ Z.homOfLE h := by
  rw [← cancel_mono U.ι]; simp

/- English proof (translation)
Establish `le : ∀ J : PUnit → A.A.ι, (A.A.pull f).U J ≤ f ⁻¹ᵁ A.A.U (J PUnit.unit)` using `fun J _ hy => mem_pull.1 hy`. Set `e : ∀ J : PUnit → A.A.ι, (Over.mk ((A.A.pull f).U J).ι).left ⟶ (Over.mk (A.A.U (J PUnit.unit)).ι).left` to `fun J => f.resLE _ _ (le J)`. Establish `he : ∀ J, e J ≫ (Over.mk (A.A.U (J PUnit.unit)).ι).hom = (Over.mk ((A.A.pull f).U J).ι).hom ≫ f` using `fun J => f.resLE_comp_ι _`. Use `choose th hth using fun J => exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ (e J) (he J)) (A.th (J PUnit.unit))`. Use `choose b hb using fun J k => exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ (e J) (he J)) (A.b (J PUnit.unit) k)`.

Use `⟨⟨A.A.pull f, LB.isLB_linComb A.isLB _ _, fun z => ?_, A.n, th, b, A.r, A.s, fun J J' => ?_, fun J W _ _ _ hW χ hχ => ?_⟩, rfl, rfl⟩` and prove the remaining obligations. Take `⟨d, s, hd, hz, ha⟩` from `A.ample (f z)`. Set `a` to `chartPullLinComb A.A f (K := Fin 1) (fun _ => 𝟙 Z') (fun _ => 𝟙 Z) (fun _ => (d : ℤ)) f (fun _ => by rw [Category.id_comp, Category.comp_id])`. Establish `hl : nonzeroLocus (chartSec a s) = f ⁻¹ᵁ nonzeroLocus s` using `nonzeroLocus_chartSec a s fun y _ _ => by`. Take `⟨i, hi⟩` from `exists_chart A.isLB (f y)`.

Conclude with `⟨fun _ _ => i, Set.mem_iInter.2 fun _ => mem_pull.2 hi⟩`. Use `⟨d, chartSec a s, hd, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hl.ge hz`. Conclude with `hl ▸ ha.preimage f`. Take `⟨c, M, ⟨t, t₁, t₂⟩, hk, hg⟩` from `A.trans (J PUnit.unit) (J' PUnit.unit)`.

Establish `le₂ : (A.A.pull f).U J ⊓ (A.A.pull f).U J' ≤ f ⁻¹ᵁ (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit))` using `fun _ hy => ⟨le J hy.1, le J' hy.2⟩`. Set `e₁ : (Over.mk ((A.A.pull f).U J ⊓ (A.A.pull f).U J').ι).left ⟶ (Over.mk (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit)).ι).left` to `f.resLE _ _ le₂`. Establish `he₁ : e₁ ≫ (Over.mk (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit)).ι).hom = (Over.mk ((A.A.pull f).U J ⊓ (A.A.pull f).U J').ι).hom ≫ f` using `f.resLE_comp_ι _`. Establish `s₁` using `kap_sq hP.w he₁ (he J) (Over.homMk (Z'.homOfLE inf_le_left) (by simp)) (Over.homMk (Z.homOfLE inf_le_left) (by simp)) (res_sq (le J) le₂ inf_le_left inf_le_left)`. Establish `s₂` using `kap_sq hP.w he₁ (he J') (Over.homMk (Z'.homOfLE inf_le_right) (by simp)) (Over.homMk (Z.homOfLE inf_le_right) (by simp)) (res_sq (le J') le₂ inf_le_right inf_le_right)`.

Establish `o : (fun _ : Fin 1 => e₁.appTop.hom 1) = fun _ => 1` using `funext fun _ => map_one _`. Use `⟨Units.map e₁.appTop.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map e₁.appTop.hom M, ?_, fun k => ?_, ?_⟩` and prove the remaining obligations. Take `⟨t', R⟩` from `exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ e₁ he₁) t`. Conclude with `⟨t', o ▸ lin_down hL s₁ (kap_fst _ _ _ _ _) R (fun _ => hth J) t₁, lin_down hL s₂ (kap_fst _ _ _ _ _) R (fun _ => hth J') t₂⟩`. Take `⟨t, t₁, t₂⟩` from `hk k`.

Take `⟨t', R⟩` from `exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ e₁ he₁) t`. Conclude with `⟨t', o ▸ lin_down hL s₁ (kap_fst _ _ _ _ _) R (fun _ => hb J k) t₁, lin_down hL s₂ (kap_fst _ _ _ _ _) R (hb J') t₂⟩`. Establish `g₁ : ((A.A.pull f).g J J').val = (f.appLE _ _ le₂).hom (A.A.g (J PUnit.unit) (J' PUnit.unit)).val` using `by show (∏ _k : PUnit, (res le₂ (pullU f _ (A.A.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)).val = _`. Rewrite using `[Fintype.prod_unique, zpow_one]`. Both sides reduce to the same expression.

Establish `g₂ : (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit)).topIso.inv ≫ e₁.appTop = f.appLE _ _ le₂ ≫ ((A.A.pull f).U J ⊓ (A.A.pull f).U J').topIso.inv` using `by show _ ≫ (f.resLE _ _ le₂).app ⊤ = _`. Rewrite using `[Scheme.Hom.resLE_app_top]`. Conclude with `Iso.inv_hom_id_assoc _ _`. Establish `g₃` using `congrArg (fun q => q.hom (A.A.g (J PUnit.unit) (J' PUnit.unit)).val) g₂`. Rewrite using `[g₁]`.

Use `g₃.symm.trans ((congrArg e₁.appTop.hom hg).trans ?_)` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.map_det]`. Conclude with `congrArg Units.val ((map_mul (Units.map e₁.appTop.hom.toMonoidHom) _ _).trans (congrArg₂ (· * ·) (map_zpow _ _ _) (map_zpow _ _ _)))`. Establish `hab : Set.range (jK W ≫ (χ ≫ e J) ≫ (A.A.U (J PUnit.unit)).ι) ⊆ abLocus G`. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `q : jK W ≫ (χ ≫ e J) ≫ (A.A.U (J PUnit.unit)).ι = (jK W ≫ χ ≫ ((A.A.pull f).U J).ι) ≫ f`. Simplify using `only [Category.assoc]`. Conclude with `congrArg (fun q => jK W ≫ χ ≫ q) (he J)`. Rewrite using `[q]`. Conclude with `(abLocus_pullback abLocusOne hG hP _).2 (hχ ⟨x, rfl⟩)`.

Take `⟨B₁, B₂⟩` from `A.trait (J PUnit.unit) W hW (χ ≫ e J) hab`. Conclude with `⟨basis_down hP hw hL hL' (he J) χ (fun _ => hth J) B₁, basis_down hP hw hL hL' (he J) χ (hb J) B₂⟩`.
-/
theorem exists_pull [GrpObj G] (hG : IsSemiAbelian G) (hP : IsPullback φ G'.hom G.hom f) (hw : PGen w) (hL : L.IsLB)
    (hL' : L'.IsLB) [IsAffineHom f] {N : ℕ} (A : AmpFrames G L N) :
    ∃ A' : AmpFrames G' L' N, A'.r = A.r ∧ A'.s = A.s := by
  have le : ∀ J : PUnit → A.A.ι, (A.A.pull f).U J ≤ f ⁻¹ᵁ A.A.U (J PUnit.unit) := fun J _ hy => mem_pull.1 hy
  let e : ∀ J : PUnit → A.A.ι, (Over.mk ((A.A.pull f).U J).ι).left ⟶ (Over.mk (A.A.U (J PUnit.unit)).ι).left :=
    fun J => f.resLE _ _ (le J)
  have he : ∀ J, e J ≫ (Over.mk (A.A.U (J PUnit.unit)).ι).hom = (Over.mk ((A.A.pull f).U J).ι).hom ≫ f :=
    fun J => f.resLE_comp_ι _
  choose th hth using fun J => exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ (e J) (he J)) (A.th (J PUnit.unit))
  choose b hb using fun J k => exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ (e J) (he J)) (A.b (J PUnit.unit) k)
  refine ⟨⟨A.A.pull f, LB.isLB_linComb A.isLB _ _, fun z => ?_, A.n, th, b, A.r, A.s, fun J J' => ?_,
    fun J W _ _ _ hW χ hχ => ?_⟩, rfl, rfl⟩
  · obtain ⟨d, s, hd, hz, ha⟩ := A.ample (f z)
    let a := chartPullLinComb A.A f (K := Fin 1) (fun _ => 𝟙 Z') (fun _ => 𝟙 Z) (fun _ => (d : ℤ)) f
      (fun _ => by rw [Category.id_comp, Category.comp_id])
    have hl : nonzeroLocus (chartSec a s) = f ⁻¹ᵁ nonzeroLocus s := nonzeroLocus_chartSec a s fun y _ _ => by
      obtain ⟨i, hi⟩ := exists_chart A.isLB (f y)
      exact ⟨fun _ _ => i, Set.mem_iInter.2 fun _ => mem_pull.2 hi⟩
    refine ⟨d, chartSec a s, hd, ?_, ?_⟩
    · exact hl.ge hz
    · exact hl ▸ ha.preimage f
  · obtain ⟨c, M, ⟨t, t₁, t₂⟩, hk, hg⟩ := A.trans (J PUnit.unit) (J' PUnit.unit)
    have le₂ : (A.A.pull f).U J ⊓ (A.A.pull f).U J' ≤ f ⁻¹ᵁ (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit)) :=
      fun _ hy => ⟨le J hy.1, le J' hy.2⟩
    let e₁ : (Over.mk ((A.A.pull f).U J ⊓ (A.A.pull f).U J').ι).left ⟶
        (Over.mk (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit)).ι).left := f.resLE _ _ le₂
    have he₁ : e₁ ≫ (Over.mk (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit)).ι).hom =
        (Over.mk ((A.A.pull f).U J ⊓ (A.A.pull f).U J').ι).hom ≫ f := f.resLE_comp_ι _
    have s₁ := kap_sq hP.w he₁ (he J) (Over.homMk (Z'.homOfLE inf_le_left) (by simp))
      (Over.homMk (Z.homOfLE inf_le_left) (by simp)) (res_sq (le J) le₂ inf_le_left inf_le_left)
    have s₂ := kap_sq hP.w he₁ (he J') (Over.homMk (Z'.homOfLE inf_le_right) (by simp))
      (Over.homMk (Z.homOfLE inf_le_right) (by simp)) (res_sq (le J') le₂ inf_le_right inf_le_right)
    have o : (fun _ : Fin 1 => e₁.appTop.hom 1) = fun _ => 1 := funext fun _ => map_one _
    refine ⟨Units.map e₁.appTop.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map e₁.appTop.hom M, ?_, fun k => ?_, ?_⟩
    · obtain ⟨t', R⟩ := exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ e₁ he₁) t
      exact ⟨t', o ▸ lin_down hL s₁ (kap_fst _ _ _ _ _) R (fun _ => hth J) t₁,
        lin_down hL s₂ (kap_fst _ _ _ _ _) R (fun _ => hth J') t₂⟩
    · obtain ⟨t, t₁, t₂⟩ := hk k
      obtain ⟨t', R⟩ := exists_rel_down hw hL hL' _ (kap_snd hP.w _ _ e₁ he₁) t
      exact ⟨t', o ▸ lin_down hL s₁ (kap_fst _ _ _ _ _) R (fun _ => hb J k) t₁,
        lin_down hL s₂ (kap_fst _ _ _ _ _) R (hb J') t₂⟩
    · have g₁ : ((A.A.pull f).g J J').val = (f.appLE _ _ le₂).hom (A.A.g (J PUnit.unit) (J' PUnit.unit)).val := by
        show (∏ _k : PUnit, (res le₂ (pullU f _ (A.A.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)).val = _
        rw [Fintype.prod_unique, zpow_one]; rfl
      have g₂ : (A.A.U (J PUnit.unit) ⊓ A.A.U (J' PUnit.unit)).topIso.inv ≫ e₁.appTop =
          f.appLE _ _ le₂ ≫ ((A.A.pull f).U J ⊓ (A.A.pull f).U J').topIso.inv := by
        show _ ≫ (f.resLE _ _ le₂).app ⊤ = _
        rw [Scheme.Hom.resLE_app_top]; exact Iso.inv_hom_id_assoc _ _
      have g₃ := congrArg (fun q => q.hom (A.A.g (J PUnit.unit) (J' PUnit.unit)).val) g₂
      rw [g₁]
      refine g₃.symm.trans ((congrArg e₁.appTop.hom hg).trans ?_)
      rw [Matrix.GeneralLinearGroup.map_det]
      exact congrArg Units.val ((map_mul (Units.map e₁.appTop.hom.toMonoidHom) _ _).trans
        (congrArg₂ (· * ·) (map_zpow _ _ _) (map_zpow _ _ _)))
  · have hab : Set.range (jK W ≫ (χ ≫ e J) ≫ (A.A.U (J PUnit.unit)).ι) ⊆ abLocus G := by
      rintro _ ⟨x, rfl⟩
      have q : jK W ≫ (χ ≫ e J) ≫ (A.A.U (J PUnit.unit)).ι = (jK W ≫ χ ≫ ((A.A.pull f).U J).ι) ≫ f := by
        simp only [Category.assoc]; exact congrArg (fun q => jK W ≫ χ ≫ q) (he J)
      rw [q]
      exact (abLocus_pullback abLocusOne hG hP _).2 (hχ ⟨x, rfl⟩)
    obtain ⟨B₁, B₂⟩ := A.trait (J PUnit.unit) W hW (χ ≫ e J) hab
    exact ⟨basis_down hP hw hL hL' (he J) χ (fun _ => hth J) B₁, basis_down hP hw hL hL' (he J) χ (hb J) B₂⟩

/- English proof (translation)
Take `⟨w, hw, -⟩` from `(isPullCubical_iff m.cm t.cub t'.cub).1 m.lin`. Conclude with `exists_pull t.semi m.cart.1 hw t.PP.isLB t'.PP.isLB A`.
-/
theorem ampFrames_pull (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z' : Scheme.{0}) (t : SAB H Z)
    (t' : SAB H Z') (f : Z' ⟶ Z) (m : SABMap t' t f) (N : ℕ) (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N) (hf : IsAffineHom f) :
    ∃ A' : GlobalTheory.LN.AmpFrames t'.G t'.PP.L N, A'.r = A.r ∧ A'.s = A.s := by
  obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
  exact exists_pull t.semi m.cart.1 hw t.PP.isLB t'.PP.isLB A

end GlobalTheory.AmpPull

end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

/- English proof (translation)
The claim follows from `GlobalTheory.AmpPull.ampFrames_pull`.
-/
theorem GlobalTheory.AmpPull.ampFrames_pull_of_isAffineHom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z' : Scheme.{0}) (t : SAB H Z) (t' : SAB H Z') (f : Z' ⟶ Z) (_ : SABMap t' t f) (N : ℕ) (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N), IsAffineHom f → ∃ A' : GlobalTheory.LN.AmpFrames t'.G t'.PP.L N, A'.r = A.r ∧ A'.s = A.s :=
  GlobalTheory.AmpPull.ampFrames_pull

end
