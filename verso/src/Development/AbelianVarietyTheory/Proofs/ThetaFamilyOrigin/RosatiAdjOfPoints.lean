import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjMul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace IntAct

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

/- English proof (translation)
Introduce `s`. Take `⟨U, hs, hU⟩` from `h s`. Use `⟨U, hs, ?_⟩` and prove the remaining obligations. Set `W : (A ⊗ A).left.Opens` to `(A ⊗ A).hom ⁻¹ᵁ U`. Set `T : Over S` to `Over.mk (W.ι ≫ (A ⊗ A).hom)`.

Set `ρ : T ⟶ A ⊗ A` to `Over.homMk W.ι rfl`. Take `⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι` from `⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩`. Take `⟨K, _, φ, ε, t, ht, hf⟩` from `hU T x y (fun p => p.2)`. Take `⟨u, hu, -⟩` from `exists_gen hL (φ' := fun i => W.ι ≫ rosatiφ A f g i) (ε' := rosatiε) (fun V _ k => (hf V k).trans ((prod_ros f g x y k).symm.trans (Finset.prod_congr rfl fun i _ => by rw [hxy]))) t ht`. Conclude with `⟨u, hu⟩`.
-/
theorem rosatiAdj_of_points (hL : L.IsLB) (f g : A ⟶ A)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∀ (T : Over S) (x y : T ⟶ A), (∀ p, T.hom p ∈ U) →
      ∃ (K : Type) (_ : Fintype K) (φ : K → (T.left ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
        t.IsGen ∧ ∀ (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V), ∏ i, k (φ i) ^ ε i =
          k ((x ≫ f) * y).left * (k (x ≫ f).left)⁻¹ * (k y.left)⁻¹ * (k (x * (y ≫ g)).left)⁻¹ * k x.left *
            k (y ≫ g).left) : RosatiAdj A L f g := by
  intro s
  obtain ⟨U, hs, hU⟩ := h s
  refine ⟨U, hs, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ U
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  obtain ⟨K, _, φ, ε, t, ht, hf⟩ := hU T x y (fun p => p.2)
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := fun i => W.ι ≫ rosatiφ A f g i) (ε' := rosatiε)
    (fun V _ k => (hf V k).trans ((prod_ros f g x y k).symm.trans
      (Finset.prod_congr rfl fun i _ => by rw [hxy]))) t ht
  exact ⟨u, hu⟩

/- English proof (translation)
Introduce `_ _` and use `(map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm`.
-/
theorem isGen_oneGen {X Y : Scheme.{0}} (M : LB X) : (LB.oneGen M (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

/- English proof (translation)
The claim follows from `rosatiAdj_of_points hL _ _ fun _ => ⟨⊤, trivial, fun T x y _ => ⟨PEmpty, inferInstance, _, _, LB.oneGen L, isGen_oneGen L, fun V _ k => by rw [MonObj.comp_one, MonObj.comp_one, _root_.one_mul, _root_.mul_one, Fintype.prod_empty] apply Additive.ofMul.injective simp only [ofMul_mul …`.
-/
theorem rosatiAdj_one (hL : L.IsLB) : RosatiAdj A L 1 1 :=
  rosatiAdj_of_points hL _ _ fun _ => ⟨⊤, trivial, fun T x y _ =>
    ⟨PEmpty, inferInstance, _, _, LB.oneGen L, isGen_oneGen L, fun V _ k => by
      rw [MonObj.comp_one, MonObj.comp_one, _root_.one_mul, _root_.mul_one, Fintype.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel⟩⟩

/- English proof (translation)
The claim follows from `rosatiAdj_of_points hL _ _ fun _ => ⟨⊤, trivial, fun T x y _ => ⟨PEmpty, inferInstance, _, _, LB.oneGen L, isGen_oneGen L, fun V _ k => by rw [Category.comp_id, Category.comp_id, Fintype.prod_empty] apply Additive.ofMul.injective simp only [ofMul_mul, ofMul_inv, ofMul_one] abel⟩⟩`.
-/
theorem rosatiAdj_id (hL : L.IsLB) : RosatiAdj A L (𝟙 A) (𝟙 A) :=
  rosatiAdj_of_points hL _ _ fun _ => ⟨⊤, trivial, fun T x y _ =>
    ⟨PEmpty, inferInstance, _, _, LB.oneGen L, isGen_oneGen L, fun V _ k => by
      rw [Category.comp_id, Category.comp_id, Fintype.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel⟩⟩

/- English proof (translation)
Use `rosatiAdj_of_points hL _ _ fun s => ?_` and prove the remaining obligations. Take `⟨U, hU, t, ht⟩` from `hs s`. Use `⟨U, hU, fun T x y hT => ?_⟩` and prove the remaining obligations. Establish `lf : ∀ w : T ⟶ A, ∃ m : T.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, m ≫ (A.hom ⁻¹ᵁ U).ι = w.left` using `fun w => ⟨IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι w.left (by`. Introduce and unpack `_ ⟨p, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Establish `e` using `congrArg (fun q => q p) (Over.w w)`. Conclude with `(congrArg (· ∈ U) e).mpr (hT p)), IsOpenImmersion.lift_fac _ _ _⟩`. Use `choose m hm using lf`. Establish `pr : ∀ (w : T ⟶ A) (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V), ∏ i : Fin 2, k (m w ≫ (![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] : Fin 2 → ((A.hom ⁻¹ᵁ U).toScheme ⟶ A.left)) i) ^ (![1, -1] : Fin 2 → ℤ) i = k (w⁻¹).left * (k w.left)⁻¹` using `fun w V _ k => by`.

Rewrite using `[Fin.prod_univ_two]`. Use `show k (m w ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) * k (m w ≫ (A.hom ⁻¹ᵁ U).ι) ^ (-1 : ℤ) = _`. Rewrite using `[← Category.assoc, hm, zpow_one, zpow_neg_one]`. Both sides reduce to the same expression. Use `⟨(Fin 2 ⊕ Fin 2) ⊕ Fin 2, inferInstance, _, _, LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ t (m (x * y⁻¹))) (LB.pullGen L _ _ t (m y))) (LB.invGen L _ _ (LB.pullGen L _ _ t (m x))), DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ …` and prove the remaining obligations.

Use `(DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := V) _ (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (pr (x * y⁻¹) V k) (pr y V k)) (DVR.prod_neg _ _ (pr x V k))).trans ?_` and prove the remaining obligations. Establish `e : ∀ w : T ⟶ A, w ≫ (𝟙 A)⁻¹ = w⁻¹` using `fun w => by rw [GrpObj.comp_inv, Category.comp_id]`. Rewrite using `[e, e, mul_inv, inv_inv]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, mul_inv, inv_inv]`.

Normalize the expressions using the abelian group laws.
-/
theorem rosatiAdj_inv (hL : L.IsLB) (hs : Out.Sym A L) : RosatiAdj A L (𝟙 A)⁻¹ (𝟙 A)⁻¹ := by
  refine rosatiAdj_of_points hL _ _ fun s => ?_
  obtain ⟨U, hU, t, ht⟩ := hs s
  refine ⟨U, hU, fun T x y hT => ?_⟩
  have lf : ∀ w : T ⟶ A, ∃ m : T.left ⟶ (A.hom ⁻¹ᵁ U).toScheme, m ≫ (A.hom ⁻¹ᵁ U).ι = w.left := fun w =>
    ⟨IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι w.left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have e := congrArg (fun q => q p) (Over.w w)
      exact (congrArg (· ∈ U) e).mpr (hT p)), IsOpenImmersion.lift_fac _ _ _⟩
  choose m hm using lf
  have pr : ∀ (w : T ⟶ A) (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V),
      ∏ i : Fin 2, k (m w ≫ (![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] :
        Fin 2 → ((A.hom ⁻¹ᵁ U).toScheme ⟶ A.left)) i) ^ (![1, -1] : Fin 2 → ℤ) i =
        k (w⁻¹).left * (k w.left)⁻¹ := fun w V _ k => by
    rw [Fin.prod_univ_two]
    show k (m w ≫ (A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) *
      k (m w ≫ (A.hom ⁻¹ᵁ U).ι) ^ (-1 : ℤ) = _
    rw [← Category.assoc, hm, zpow_one, zpow_neg_one]
    rfl
  refine ⟨(Fin 2 ⊕ Fin 2) ⊕ Fin 2, inferInstance, _, _,
    LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ t (m (x * y⁻¹))) (LB.pullGen L _ _ t (m y)))
      (LB.invGen L _ _ (LB.pullGen L _ _ t (m x))),
    DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)), fun V _ k => ?_⟩
  refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := V) _
    (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (pr (x * y⁻¹) V k) (pr y V k))
    (DVR.prod_neg _ _ (pr x V k))).trans ?_
  have e : ∀ w : T ⟶ A, w ≫ (𝟙 A)⁻¹ = w⁻¹ := fun w => by rw [GrpObj.comp_inv, Category.comp_id]
  rw [e, e, mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, mul_inv, inv_inv]
  abel

/- English proof (translation)
Proceed by induction on `a using Int.induction_on with`. Consider the case `zero => rw [zpow_zero]`. Conclude with `rosatiAdj_one M.isLB`. Consider the case `succ n ih => rw [zpow_add_one]`. Conclude with `rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_id M.isLB)`.

Consider the case `pred n ih => rw [zpow_sub_one]`. Conclude with `rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_inv M.isLB hs)`.
-/
theorem rosatiAdj_zpow (M : RigLB A) (c : CubicalStr A M) (hs : Out.Sym A M.L) (a : ℤ) :
    RosatiAdj A M.L ((𝟙 A) ^ a) ((𝟙 A) ^ a) := by
  induction a using Int.induction_on with
  | zero => rw [zpow_zero]; exact rosatiAdj_one M.isLB
  | succ n ih => rw [zpow_add_one]; exact rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_id M.isLB)
  | pred n ih => rw [zpow_sub_one]; exact rosatiAdj_mul S A M c _ _ _ _ ih (rosatiAdj_inv M.isLB hs)

/- English proof (translation)
Rewrite using `[GrpObj.comp_zpow, Category.comp_id]`.
-/
theorem comp_id_zpow {T : Over S} (w : T ⟶ A) (a : ℤ) : w ≫ (𝟙 A) ^ a = w ^ a := by
  rw [GrpObj.comp_zpow, Category.comp_id]

/- English proof (translation)
Rewrite using `[comp_id_zpow]`. Establish `o : η[A] = 1` using `by simp [Hom.one_def]`. Rewrite using `[o, one_zpow]`. Use `mul_hom := by`. Establish `o : μ[A] = fst A A * snd A A` using `by simp [Hom.mul_def]`.

Rewrite using `[comp_id_zpow, o, mul_zpow, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, comp_id_zpow, comp_id_zpow]`.
-/
theorem isMonHom_id_zpow (a : ℤ) : IsMonHom ((𝟙 A : A ⟶ A) ^ a) where
  one_hom := by
    rw [comp_id_zpow]
    have o : η[A] = 1 := by simp [Hom.one_def]
    rw [o, one_zpow]
  mul_hom := by
    have o : μ[A] = fst A A * snd A A := by simp [Hom.mul_def]
    rw [comp_id_zpow, o, mul_zpow, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, comp_id_zpow, comp_id_zpow]

variable (A) in

def intRingAct : RingAct A ℤ where
  act a := (𝟙 A) ^ a
  hom := isMonHom_id_zpow
  map_one := zpow_one _
  map_mul a b := by rw [comp_id_zpow, ← zpow_mul, _root_.mul_comm]
  map_add a b := zpow_add _ a b

end IntAct

/- English proof (translation)
Introduce `hC S _ P`. Take `⟨r, hr⟩` from `P.rigid`. Take `⟨c⟩` from `(hC S P ⟨P.L, r, P.isLB, hr⟩ rfl).1`. Conclude with `⟨⟨IntAct.intRingAct P.A, fun a => IntAct.rosatiAdj_zpow ⟨P.L, r, P.isLB, hr⟩ c P.sym a⟩, fun _ => rfl⟩`.
-/
theorem exists_oAct_int : Out.CubeSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S),
    ∃ ρ : P.OAct ℤ, ∀ a : ℤ, ρ.act a = (𝟙 P.A : P.A ⟶ P.A) ^ a := by
  intro hC S _ P
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hC S P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  exact ⟨⟨IntAct.intRingAct P.A, fun a => IntAct.rosatiAdj_zpow ⟨P.L, r, P.isLB, hr⟩ c P.sym a⟩, fun _ => rfl⟩

end GlobalTheory
