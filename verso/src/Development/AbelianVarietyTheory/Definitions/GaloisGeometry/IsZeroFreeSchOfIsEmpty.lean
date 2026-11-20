import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Tr

section Transfer

variable (R : Type) [CommRing R]

abbrev freeSch (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

def IsTransfer {Z X : Scheme.{0}} (f : Z ⟶ X) (t : freeSch R X ⟶ freeSch R Z) : Prop :=
  ∀ (S : Scheme.{0}) (x : S ⟶ X) (m : ℕ) (s : Fin m → (S ⟶ Z)) (hs : ∀ j, s j ≫ f = x),
    IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => S) ⟶ pullback f x) →
    (free R).map (yoneda.map x) ≫ t = ∑ j, (free R).map (yoneda.map (s j))

def transfer {Z X : Scheme.{0}} (f : Z ⟶ X) : freeSch R X ⟶ freeSch R Z := pick (IsTransfer R f)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
/- English proof (translation)
The claim follows from `_root_.GlobalTheory.EtC.pick_spec h`.
-/
theorem _root_.GlobalTheory.EtC.Tr.transfer_spec {Z X : Scheme.{0}} {f : Z ⟶ X}
    (h : ∃ t, _root_.GlobalTheory.EtC.Tr.IsTransfer R f t) :
    _root_.GlobalTheory.EtC.Tr.IsTransfer R f (_root_.GlobalTheory.EtC.Tr.transfer R f) :=
  _root_.GlobalTheory.EtC.pick_spec h

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Apply `((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv ((freeP R).obj (yoneda.obj X)) (freeSch R X)).injective` to reduce the goal to its premises. Apply `NatTrans.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Break down `isEmpty_or_nonempty U.unop with hU | hU` into its components or cases. Establish `hb : (⊥ : Sieve U.unop) ∈ Scheme.etaleTopology U.unop` using `Scheme.bot_mem_grothendieckTopology U.unop`. Conclude with `Sheaf.isSeparated (freeSch R X) U.unop ⊥ hb _ _ (fun _ _ h => h.elim)`.

Establish `: IsEmpty (ULift.{1} (U.unop ⟶ X))` using `⟨fun f => IsEmpty.false (f.down.base (Classical.arbitrary U.unop))⟩`. Establish `hs : Subsingleton (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R)` using `inferInstance`. Establish `hx : x = 0` using `hs.elim x 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.
-/
theorem isZero_freeSch_of_isEmpty (X : Scheme.{0}) [IsEmpty X] : IsZero (freeSch R X) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (yoneda.obj X)) (freeSch R X)).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have hb : (⊥ : Sieve U.unop) ∈ Scheme.etaleTopology U.unop := Scheme.bot_mem_grothendieckTopology U.unop
    exact Sheaf.isSeparated (freeSch R X) U.unop ⊥ hb _ _ (fun _ _ h => h.elim)
  · have : IsEmpty (ULift.{1} (U.unop ⟶ X)) :=
      ⟨fun f => IsEmpty.false (f.down.base (Classical.arbitrary U.unop))⟩
    have hs : Subsingleton (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R) := inferInstance
    have hx : x = 0 := hs.elim x 0
    subst hx
    simp

/- English proof (translation)
Break down `Nat.lt_trichotomy m 1 with hm | hm | hm` into its components or cases. Establish `hm0 : m = 0` using `by omega`. Substitute `hm0` using the available equality. Establish `f : S ⟶ (∅ : Scheme.{0})` using `inv (Sigma.desc (fun _ : Fin 0 => 𝟙 S)) ≫ Sigma.desc (fun j : Fin 0 => j.elim0)`. Conclude with `(IsEmpty.false (f pt)).elim`.

Conclude with `hm`. It suffices to derive a contradiction. Set `i : Fin m` to `⟨0, by omega⟩`. Set `j : Fin m` to `⟨1, hm⟩`. Establish `hij : Sigma.ι (fun _ : Fin m => S) i = Sigma.ι (fun _ : Fin m => S) j` using `(cancel_mono (Sigma.desc (fun _ : Fin m => 𝟙 S))).1 (by simp)`.

Establish `hp : Sigma.ι (fun _ : Fin m => S) i pt = Sigma.ι (fun _ : Fin m => S) j pt` using `by rw [hij]`. Use `congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => S) i j pt pt).mp hp)` as an intermediate fact. Simplify using `[i, j] at this`.
-/
theorem eq_one_of_isIso_codiag {S : Scheme.{0}} (pt : S) {m : ℕ}
    (h : IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S)) : m = 1 := by
  rcases Nat.lt_trichotomy m 1 with hm | hm | hm
  · have hm0 : m = 0 := by omega
    subst hm0
    have f : S ⟶ (∅ : Scheme.{0}) :=
      inv (Sigma.desc (fun _ : Fin 0 => 𝟙 S)) ≫ Sigma.desc (fun j : Fin 0 => j.elim0)
    exact (IsEmpty.false (f pt)).elim
  · exact hm
  · exfalso
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, hm⟩
    have hij : Sigma.ι (fun _ : Fin m => S) i = Sigma.ι (fun _ : Fin m => S) j :=
      (cancel_mono (Sigma.desc (fun _ : Fin m => 𝟙 S))).1 (by simp)
    have hp : Sigma.ι (fun _ : Fin m => S) i pt = Sigma.ι (fun _ : Fin m => S) j pt := by rw [hij]
    have := congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => S) i j pt pt).mp hp)
    simp [i, j] at this

/- English proof (translation)
Introduce `S x m s hs hiso`. Establish `hsx : ∀ j, s j = x` using `fun j => by simpa using hs j`. Simplify using `only [Category.comp_id, hsx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Break down `isEmpty_or_nonempty S with hS | hS` into its components or cases. Conclude with `(isZero_freeSch_of_isEmpty R S).eq_of_src _ _`.

Take `⟨pt⟩` from `hS`. Establish `hc : (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) : ∐ (fun _ : Fin m => S) ⟶ pullback (𝟙 X) x) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin m => 𝟙 S)`. Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `j`. Rewrite using `[Sigma.ι_desc_assoc, Sigma.ι_desc]`.

Conclude with `pullback.lift_snd _ _ _`. Establish `: IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S)`. Rewrite using `[← hc]`. Use `infer_instance`. Rewrite using `[eq_one_of_isIso_codiag pt this, one_smul]`.
-/
theorem isTransfer_id (X : Scheme.{0}) : IsTransfer R (𝟙 X) (𝟙 _) := by
  intro S x m s hs hiso
  have hsx : ∀ j, s j = x := fun j => by simpa using hs j
  simp only [Category.comp_id, hsx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rcases isEmpty_or_nonempty S with hS | hS
  · exact (isZero_freeSch_of_isEmpty R S).eq_of_src _ _
  · obtain ⟨pt⟩ := hS
    have hc : (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) :
        ∐ (fun _ : Fin m => S) ⟶ pullback (𝟙 X) x) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin m => 𝟙 S) := by
      apply Sigma.hom_ext; intro j; rw [Sigma.ι_desc_assoc, Sigma.ι_desc]; exact pullback.lift_snd _ _ _
    have : IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S) := by
      rw [← hc]; infer_instance
    rw [eq_one_of_isIso_codiag pt this, one_smul]

/- English proof (translation)
Establish `hcod : IsIso (Sigma.desc (fun _ : Fin 1 => 𝟙 X) : ∐ (fun _ : Fin 1 => X) ⟶ X)` using `⟨⟨Sigma.ι (fun _ : Fin 1 => X) 0, by ext j; fin_cases j; simp, by simp⟩⟩`. Establish `hc : (Sigma.desc (fun _ : Fin 1 => pullback.lift (𝟙 X) (𝟙 X) (by simp)) : ∐ (fun _ : Fin 1 => X) ⟶ pullback (𝟙 X) (𝟙 X)) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin 1 => 𝟙 X)`. Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `j`. Rewrite using `[Sigma.ι_desc_assoc, Sigma.ι_desc]`.

Conclude with `pullback.lift_snd _ _ _`. Establish `hiso : IsIso (Sigma.desc (fun _ : Fin 1 => pullback.lift (𝟙 X) (𝟙 X) (by simp)) : ∐ (fun _ : Fin 1 => X) ⟶ pullback (𝟙 X) (𝟙 X))`. Rewrite `hcod` using `[← hc]`. Conclude with `IsIso.of_isIso_comp_right _ (pullback.snd (𝟙 X) (𝟙 X))`. Use `ht X (𝟙 X) 1 (fun _ => 𝟙 X) (fun _ => by simp) hiso` as an intermediate fact.

Simplify using `using this`.
-/
theorem eq_id_of_isTransfer_id {X : Scheme.{0}} {t : freeSch R X ⟶ freeSch R X} (ht : IsTransfer R (𝟙 X) t) : t = 𝟙 _ := by
  have hcod : IsIso (Sigma.desc (fun _ : Fin 1 => 𝟙 X) : ∐ (fun _ : Fin 1 => X) ⟶ X) :=
    ⟨⟨Sigma.ι (fun _ : Fin 1 => X) 0, by ext j; fin_cases j; simp, by simp⟩⟩
  have hc : (Sigma.desc (fun _ : Fin 1 => pullback.lift (𝟙 X) (𝟙 X) (by simp)) :
      ∐ (fun _ : Fin 1 => X) ⟶ pullback (𝟙 X) (𝟙 X)) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin 1 => 𝟙 X) := by
    apply Sigma.hom_ext; intro j; rw [Sigma.ι_desc_assoc, Sigma.ι_desc]; exact pullback.lift_snd _ _ _
  have hiso : IsIso (Sigma.desc (fun _ : Fin 1 => pullback.lift (𝟙 X) (𝟙 X) (by simp)) :
      ∐ (fun _ : Fin 1 => X) ⟶ pullback (𝟙 X) (𝟙 X)) := by
    rw [← hc] at hcod
    exact IsIso.of_isIso_comp_right _ (pullback.snd (𝟙 X) (𝟙 X))
  have := ht X (𝟙 X) 1 (fun _ => 𝟙 X) (fun _ => by simp) hiso
  simpa using this

/- English proof (translation)
The claim follows from `eq_id_of_isTransfer_id R (transfer_spec R ⟨_, isTransfer_id R X⟩)`.
-/
theorem transfer_id (X : Scheme.{0}) : transfer R (𝟙 X) = 𝟙 _ :=
  eq_id_of_isTransfer_id R (transfer_spec R ⟨_, isTransfer_id R X⟩)

end Transfer

section Trace

variable (R : Type) [CommRing R]

def simpMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X) ⟶
      ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj Z) where
  app _ := t
  naturality _ _ _ := by
    show (free R).map (𝟙 (yoneda.obj X)) ≫ t = t ≫ (free R).map (𝟙 (yoneda.obj Z))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

def chainMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) : (chains R).obj (sch.obj X) ⟶ (chains R).obj (sch.obj Z) :=
  (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simpMap R t))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in

/- English proof (translation)
Establish `hsimp : _root_.GlobalTheory.EtC.Tr.simpMap R ((_root_.GlobalTheory.EtC.free R).map (yoneda.map g)) = ((SimplicialObject.whiskering _ _).obj (_root_.GlobalTheory.EtC.free R)).map (_root_.GlobalTheory.EtC.sch.map g)`. Use `ext`. Both sides reduce to the same expression. Unfold `_root_.GlobalTheory.EtC.Tr.chainMap`. Rewrite using `[hsimp]`.

Both sides reduce to the same expression.
-/
lemma _root_.GlobalTheory.EtC.Tr.chainMap_free {X Z : Scheme.{0}} (g : X ⟶ Z) :
    _root_.GlobalTheory.EtC.Tr.chainMap R ((_root_.GlobalTheory.EtC.free R).map (yoneda.map g)) =
      (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.sch.map g) := by
  have hsimp : _root_.GlobalTheory.EtC.Tr.simpMap R ((_root_.GlobalTheory.EtC.free R).map (yoneda.map g)) =
      ((SimplicialObject.whiskering _ _).obj (_root_.GlobalTheory.EtC.free R)).map
        (_root_.GlobalTheory.EtC.sch.map g) := by
    ext
    rfl
  unfold _root_.GlobalTheory.EtC.Tr.chainMap
  rw [hsimp]
  rfl

def along {X Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Z) : H R (sch.obj Z) F n →+ H R (sch.obj X) F n :=
  HK.pull R (chainMap R t) F n

def alongL {X Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Z) : H R (sch.obj Z) F n →ₗ[R] H R (sch.obj X) F n where
  toFun := along R F n t
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_smul _ _ _ (zero_add n)))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
/- English proof (translation)
Establish `hid : (𝟙 (_root_.GlobalTheory.EtC.Tr.freeSch R X)) = (_root_.GlobalTheory.EtC.free R).map (yoneda.map (𝟙 X))`. Simplify using the standard rewrite rules. Rewrite using `[hid]`. Unfold `_root_.GlobalTheory.EtC.Tr.along`. Rewrite using `[_root_.GlobalTheory.EtC.Tr.chainMap_free, CategoryTheory.Functor.map_id]`.

Conclude with `_root_.GlobalTheory.EtC.pull_id R _ F n x`.
-/
theorem _root_.GlobalTheory.EtC.Tr.along_id (X : Scheme.{0}) (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ)
    (x : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.sch.obj X) F n) :
    _root_.GlobalTheory.EtC.Tr.along R F n (𝟙 _) x = x := by
  have hid : (𝟙 (_root_.GlobalTheory.EtC.Tr.freeSch R X)) =
      (_root_.GlobalTheory.EtC.free R).map (yoneda.map (𝟙 X)) := by
    simp
  rw [hid]
  unfold _root_.GlobalTheory.EtC.Tr.along
  rw [_root_.GlobalTheory.EtC.Tr.chainMap_free, CategoryTheory.Functor.map_id]
  exact _root_.GlobalTheory.EtC.pull_id R _ F n x

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in

/- English proof (translation)
Unfold `_root_.GlobalTheory.EtC.Tr.along _root_.GlobalTheory.EtC.pull`. Rewrite using `[_root_.GlobalTheory.EtC.Tr.chainMap_free]`.
-/
theorem _root_.GlobalTheory.EtC.Tr.along_free {X Z : Scheme.{0}} (g : X ⟶ Z)
    (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ) :
    _root_.GlobalTheory.EtC.Tr.along R F n ((_root_.GlobalTheory.EtC.free R).map (yoneda.map g)) =
      _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.sch.map g) F n := by
  unfold _root_.GlobalTheory.EtC.Tr.along _root_.GlobalTheory.EtC.pull
  rw [_root_.GlobalTheory.EtC.Tr.chainMap_free]

def trH {Z X : Scheme.{0}} (f : Z ⟶ X) (F : Shv R) (n : ℤ) : H R (sch.obj Z) F n →+ H R (sch.obj X) F n :=
  along R F n (transfer R f)

def trL {Z X : Scheme.{0}} (f : Z ⟶ X) (F : Shv R) (n : ℤ) : H R (sch.obj Z) F n →ₗ[R] H R (sch.obj X) F n :=
  alongL R F n (transfer R f)

/- English proof (translation)
Rewrite using `[trH, transfer_id]`. Conclude with `along_id R X F n x`.
-/
theorem trH_id (X : Scheme.{0}) (F : Shv R) (n : ℤ) (x : H R (sch.obj X) F n) : trH R (𝟙 X) F n x = x := by
  rw [trH, transfer_id]; exact along_id R X F n x

end Trace

section Twist

def trHt (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : Ht q (sch.obj Z) n i →+ Ht q (sch.obj X) n i :=
  trH (ZMod q) f (tw q i) n

/- English proof (translation)
The claim follows from `trH_id (ZMod q) X (tw q i) n x`.
-/
theorem trHt_id (q : ℕ) (X : Scheme.{0}) (n i : ℤ) (x : Ht q (sch.obj X) n i) : trHt q (𝟙 X) n i x = x :=
  trH_id (ZMod q) X (tw q i) n x

end Twist

section Adic

variable (l : ℕ) [Fact l.Prime]

def RedCompat {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : Prop :=
  ∀ (k : ℕ) (x : Ht (l ^ (k + 1)) (sch.obj Z) n i),
    red (l ^ (k + 1)) (l ^ k) (sch.obj X) n i (trHt (l ^ (k + 1)) f n i x) = trHt (l ^ k) f n i (red (l ^ (k + 1)) (l ^ k) (sch.obj Z) n i x)

def IsTrHl {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) (φ : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i) : Prop :=
  ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (φ x).1 k = trHt (l ^ k) f n i (x.1 k)

def trHl {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i :=
  pick (IsTrHl l f n i)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (l : ℕ) [Fact l.Prime] in

/- English proof (translation)
Apply `_root_.GlobalTheory.EtC.pick_spec` to reduce the goal to its premises. Use `⟨{ toFun := fun x => ⟨fun k => _root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k), ?_⟩ map_add' := ?_ map_smul' := ?_ }, fun x k => rfl⟩` and prove the remaining obligations. Introduce `k show _root_.GlobalTheory.EtC.red (l ^ (k + 1)) (l ^ k) (_root_.GlobalTheory.EtC.sch.obj X) n i (_root_.GlobalTheory.EtC.Tr.trHt (l ^ (k + 1)) f n i (x.1 (k + 1))) = _root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k)`. Rewrite using `[h k (x.1 (k + 1))]`. Use `congr 1`.

Conclude with `x.2 k`. Introduce `x y`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Conclude with `map_add (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i) (x.1 k) (y.1 k)`.

Introduce `r x`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Establish `h1` using `_root_.GlobalTheory.EtC.HtL.smul_eq l k k le_rfl (_root_.GlobalTheory.EtC.sch.obj Z) n i r (x.1 k)`. Establish `h2` using `_root_.GlobalTheory.EtC.HtL.smul_eq l k k le_rfl (_root_.GlobalTheory.EtC.sch.obj X) n i r (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k))`.

Conclude with `(congrArg (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i) h1).trans ((map_nsmul _ _ _).trans h2.symm)`.
-/
theorem _root_.GlobalTheory.EtC.Tr.trHl_spec {Z X : Scheme.{0}} {f : Z ⟶ X} {n i : ℤ}
    (h : _root_.GlobalTheory.EtC.Tr.RedCompat l f n i) :
    _root_.GlobalTheory.EtC.Tr.IsTrHl l f n i (_root_.GlobalTheory.EtC.Tr.trHl l f n i) := by
  apply _root_.GlobalTheory.EtC.pick_spec
  refine ⟨{ toFun := fun x => ⟨fun k => _root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k), ?_⟩
            map_add' := ?_
            map_smul' := ?_ }, fun x k => rfl⟩
  · intro k
    show _root_.GlobalTheory.EtC.red (l ^ (k + 1)) (l ^ k) (_root_.GlobalTheory.EtC.sch.obj X) n i
        (_root_.GlobalTheory.EtC.Tr.trHt (l ^ (k + 1)) f n i (x.1 (k + 1))) =
      _root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k)
    rw [h k (x.1 (k + 1))]
    congr 1
    exact x.2 k
  · intro x y
    apply Subtype.ext
    funext k
    exact map_add (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i) (x.1 k) (y.1 k)
  · intro r x
    apply Subtype.ext
    funext k
    have h1 := _root_.GlobalTheory.EtC.HtL.smul_eq l k k le_rfl
      (_root_.GlobalTheory.EtC.sch.obj Z) n i r (x.1 k)
    have h2 := _root_.GlobalTheory.EtC.HtL.smul_eq l k k le_rfl
      (_root_.GlobalTheory.EtC.sch.obj X) n i r (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k))
    exact (congrArg (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i) h1).trans
      ((map_nsmul _ _ _).trans h2.symm)

def trHQ {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : HQ l (sch.obj Z) n i →ₗ[ℚ_[l]] HQ l (sch.obj X) n i :=
  (trHl l f n i).baseChange ℚ_[l]

end Adic

/- English proof (translation)
The claim follows from `trHt_id 5 X n 2 x`.
-/
example (X : Scheme.{0}) (n : ℤ) (x : Ht 5 (sch.obj X) n 2) : trHt 5 (𝟙 X) n 2 x = x := trHt_id 5 X n 2 x

/- English proof (translation)
The claim follows from `transfer_id ℤ _`.
-/
example : transfer ℤ (𝟙 (Spec (CommRingCat.of (Polynomial ℤ)))) = 𝟙 _ := transfer_id ℤ _

end GlobalTheory.EtC.Tr
