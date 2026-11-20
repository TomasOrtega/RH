import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

/- English proof (translation)
Establish `h1 : (1 : A) ∈ Ideal.span (Set.range v)` using `by rw [h]; trivial`. Establish `key : ∀ c ∈ Ideal.span (Set.range v), (a - b) * c = 0`. Introduce `c hc`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨j, rfl⟩` from `hx`. Rewrite using `[sub_mul, hab, sub_self]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]`.

Establish `h2` using `key 1 h1`. Rewrite `h2` using `[mul_one]`. Conclude with `sub_eq_zero.1 h2`.
-/
private theorem unit_unique {A : Type} [CommRing A] {N : ℕ} (v : Fin N → A)
    (h : Ideal.span (Set.range v) = ⊤) (a b : A) (hab : ∀ j, a * v j = b * v j) : a = b := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range v) := by rw [h]; trivial
  have key : ∀ c ∈ Ideal.span (Set.range v), (a - b) * c = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [sub_mul, hab, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  have h2 := key 1 h1
  rw [mul_one] at h2
  exact sub_eq_zero.1 h2

/- English proof (translation)
Establish `hv : ∀ i (j : Fin d), (x i).1.1.2 j.castSucc = (y i).1.1.2 j.castSucc` using `fun i j => congrFun (congrArg (fun z => z.1.2) (h1 i)) j`. Establish `hr : ∀ i, (x i).1.1.1 = (y i).1.1.1` using `fun i => congrArg (fun z => z.1.1) (h1 i)`. Use `funext fun i => Subtype.ext (Subtype.ext (Prod.ext (hr i) (funext fun j => ?_)))` and prove the remaining obligations. Take `⟨-, u, hu⟩` from `hx i 0`. Take `⟨-, u', hu'⟩` from `hy i 0`.

Establish `huu : (u : A) = u'`. Use `unit_unique (fun j : Fin d => (x 0).1.1.2 j.castSucc) (x 0).2 _ _ fun j => ?_` and prove the remaining obligations. Establish `e1 : (x i).1.1.2 j.castSucc = (u : A) * (x 0).1.1.2 j.castSucc` using `congrFun hu _`. Establish `e2 : (y i).1.1.2 j.castSucc = (u' : A) * (y 0).1.1.2 j.castSucc` using `congrFun hu' _`. Express the relevant statement in the definitionally equal form `(u : A) * (x 0).1.1.2 j.castSucc = (u' : A) * (x 0).1.1.2 j.castSucc`.

Rewrite using `[← e1, hv i j, e2, hv 0 j]`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Establish `e1 : (x i).1.1.2 (Fin.last d) = (u : A) * (x 0).1.1.2 (Fin.last d)` using `congrFun hu _`. Establish `e2 : (y i).1.1.2 (Fin.last d) = (u' : A) * (y 0).1.1.2 (Fin.last d)` using `congrFun hu' _`. Express the relevant statement in the definitionally equal form `(x i).1.1.2 (Fin.last d) = (y i).1.1.2 (Fin.last d)`.

Rewrite using `[e1, e2, huu, h2]`. Conclude with `hv i j`.
-/
private theorem fam_inj (D : Type) [CommRing D] (d m : ℕ) {A : Type} [CommRing A]
    (x y : Fin (m + 1) → (L2 D d).obj A)
    (hx : ∀ i j, (L2 D d).rel (x i) (x j)) (hy : ∀ i j, (L2 D d).rel (y i) (y j))
    (h1 : ∀ i, (fstV D d).app A (x i) = (fstV D d).app A (y i))
    (h2 : (x 0).1.1.2 (Fin.last d) = (y 0).1.1.2 (Fin.last d)) : x = y := by
  have hv : ∀ i (j : Fin d), (x i).1.1.2 j.castSucc = (y i).1.1.2 j.castSucc :=
    fun i j => congrFun (congrArg (fun z => z.1.2) (h1 i)) j
  have hr : ∀ i, (x i).1.1.1 = (y i).1.1.1 := fun i => congrArg (fun z => z.1.1) (h1 i)
  refine funext fun i => Subtype.ext (Subtype.ext (Prod.ext (hr i) (funext fun j => ?_)))
  obtain ⟨-, u, hu⟩ := hx i 0
  obtain ⟨-, u', hu'⟩ := hy i 0
  have huu : (u : A) = u' := by
    refine unit_unique (fun j : Fin d => (x 0).1.1.2 j.castSucc) (x 0).2 _ _ fun j => ?_
    have e1 : (x i).1.1.2 j.castSucc = (u : A) * (x 0).1.1.2 j.castSucc := congrFun hu _
    have e2 : (y i).1.1.2 j.castSucc = (u' : A) * (y 0).1.1.2 j.castSucc := congrFun hu' _
    change (u : A) * (x 0).1.1.2 j.castSucc = (u' : A) * (x 0).1.1.2 j.castSucc
    rw [← e1, hv i j, e2, hv 0 j]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have e1 : (x i).1.1.2 (Fin.last d) = (u : A) * (x 0).1.1.2 (Fin.last d) := congrFun hu _
    have e2 : (y i).1.1.2 (Fin.last d) = (u' : A) * (y 0).1.1.2 (Fin.last d) := congrFun hu' _
    change (x i).1.1.2 (Fin.last d) = (y i).1.1.2 (Fin.last d)
    rw [e1, e2, huu, h2]
  · exact hv i j

/- English proof (translation)
Establish `hex : ∀ i, ∃ u : Aˣ, (c i).1.2 = fun j => (u : A) * (c 0).1.2 j` using `fun i => (hc i 0).2`. Use `choose u hu using hex`. Establish `hu0 : (u 0 : A) = 1`. Use `unit_unique (c 0).1.2 (c 0).2 _ _ fun j => ?_` and prove the remaining obligations. Establish `e : (c 0).1.2 j = (u 0 : A) * (c 0).1.2 j` using `congrFun (hu 0) j`.

Rewrite using `[← e, one_mul]`. Use `⟨fun i => ⟨⟨((c i).1.1, Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t)), span_snoc _ _ (c i).2⟩, ?_⟩, fun i j => ⟨(hc i j).1, u i * (u j)⁻¹, funext fun k => ?_⟩, fun i => Subtype.ext (Prod.ext rfl (funext fun k => ?_)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.span (Set.range fun j : Fin d => Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) j.castSucc) = ⊤`. Simplify using `using (c i).2`. Establish `hinv : ((u j : A)) * (((u j)⁻¹ : Aˣ) : A) = 1` using `Units.mul_inv _`.

Use `Fin.lastCases ?_ (fun k => ?_) k` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) (Fin.last d) = ((u i * (u j)⁻¹ : Aˣ) : A) * Fin.snoc (α := fun _ => A) (c j).1.2 ((u j : A) * t) (Fin.last d)`. Simplify using `only [Fin.snoc_last, Units.val_mul]`. Take the linear combination `(-(u i : A) * t) * hinv`. Express the relevant statement in the definitionally equal form `Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) k.castSucc = ((u i * (u j)⁻¹ : Aˣ) : A) * Fin.snoc (α := fun _ => A) (c j).1.2 ((u j : A) * t) k.castSucc`.

Simplify using `only [Fin.snoc_castSucc, Units.val_mul]`. Establish `e1 : (c i).1.2 k = (u i : A) * (c 0).1.2 k` using `congrFun (hu i) k`. Establish `e2 : (c j).1.2 k = (u j : A) * (c 0).1.2 k` using `congrFun (hu j) k`. Rewrite using `[e1, e2]`. Take the linear combination `(-(u i : A) * (c 0).1.2 k) * hinv`.

Express the relevant statement in the definitionally equal form `Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) k.castSucc = (c i).1.2 k`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `Fin.snoc (α := fun _ => A) (c 0).1.2 ((u 0 : A) * t) (Fin.last d) = t`. Simplify using `[hu0]`.
-/
private theorem fam_surj (D : Type) [CommRing D] (d m : ℕ) {A : Type} [CommRing A]
    (c : Fin (m + 1) → (Vec D d).obj A) (hc : ∀ i j, (Vec D d).rel (c i) (c j)) (t : A) :
    ∃ x : Fin (m + 1) → (L2 D d).obj A, (∀ i j, (L2 D d).rel (x i) (x j)) ∧
      (∀ i, (fstV D d).app A (x i) = c i) ∧ (x 0).1.1.2 (Fin.last d) = t := by
  have hex : ∀ i, ∃ u : Aˣ, (c i).1.2 = fun j => (u : A) * (c 0).1.2 j := fun i => (hc i 0).2
  choose u hu using hex
  have hu0 : (u 0 : A) = 1 := by
    refine unit_unique (c 0).1.2 (c 0).2 _ _ fun j => ?_
    have e : (c 0).1.2 j = (u 0 : A) * (c 0).1.2 j := congrFun (hu 0) j
    rw [← e, one_mul]
  refine ⟨fun i => ⟨⟨((c i).1.1, Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t)),
      span_snoc _ _ (c i).2⟩, ?_⟩, fun i j => ⟨(hc i j).1, u i * (u j)⁻¹, funext fun k => ?_⟩,
      fun i => Subtype.ext (Prod.ext rfl (funext fun k => ?_)), ?_⟩
  · change Ideal.span (Set.range fun j : Fin d =>
      Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) j.castSucc) = ⊤
    simpa using (c i).2
  · have hinv : ((u j : A)) * (((u j)⁻¹ : Aˣ) : A) = 1 := Units.mul_inv _
    refine Fin.lastCases ?_ (fun k => ?_) k
    · change Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) (Fin.last d) =
        ((u i * (u j)⁻¹ : Aˣ) : A) * Fin.snoc (α := fun _ => A) (c j).1.2 ((u j : A) * t) (Fin.last d)
      simp only [Fin.snoc_last, Units.val_mul]
      linear_combination (-(u i : A) * t) * hinv
    · change Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) k.castSucc =
        ((u i * (u j)⁻¹ : Aˣ) : A) * Fin.snoc (α := fun _ => A) (c j).1.2 ((u j : A) * t) k.castSucc
      simp only [Fin.snoc_castSucc, Units.val_mul]
      have e1 : (c i).1.2 k = (u i : A) * (c 0).1.2 k := congrFun (hu i) k
      have e2 : (c j).1.2 k = (u j : A) * (c 0).1.2 k := congrFun (hu j) k
      rw [e1, e2]
      linear_combination (-(u i : A) * (c 0).1.2 k) * hinv
  · change Fin.snoc (α := fun _ => A) (c i).1.2 ((u i : A) * t) k.castSucc = (c i).1.2 k
    simp
  · change Fin.snoc (α := fun _ => A) (c 0).1.2 ((u 0 : A) * t) (Fin.last d) = t
    simp [hu0]

/- English proof (translation)
Introduce `D _ d n T`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `h1` using `congrArg Prod.fst hxy`. Establish `h2 : (x.1 0).1.1.2 (Fin.last d) = (y.1 0).1.1.2 (Fin.last d)` using `congrArg Prod.snd hxy`.

Use `Subtype.ext (fam_inj D d _ x.1 y.1 x.2 y.2 (fun i => ?_) h2)` and prove the remaining obligations. Conclude with `congrFun (congrArg Subtype.val h1) i`. Introduce and unpack `⟨c, t⟩`. Take `⟨x, hx, hc, ht⟩` from `fam_surj D d _ c.1 c.2 t`. Use `⟨⟨x, hx⟩, Prod.ext (Subtype.ext (funext hc)) ht⟩` and prove the remaining obligations.
-/
theorem UpperTheory.nerve_first_projection :
    ∀ (D : Type) [CommRing D] (d : ℕ) (n : SimplexCategoryᵒᵖ) (T : Scheme.{0}), Function.Bijective fun x : ((CN (L2 D d)).obj n).obj (op T) => (((CN.map (fstV D d) (fstV_rel D d)).app n).app (op T) x, (x.1 0).1.1.2 (Fin.last d)) := by
  intro D _ d n T
  constructor
  · intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 : (x.1 0).1.1.2 (Fin.last d) = (y.1 0).1.1.2 (Fin.last d) := congrArg Prod.snd hxy
    refine Subtype.ext (fam_inj D d _ x.1 y.1 x.2 y.2 (fun i => ?_) h2)
    exact congrFun (congrArg Subtype.val h1) i
  · rintro ⟨c, t⟩
    obtain ⟨x, hx, hc, ht⟩ := fam_surj D d _ c.1 c.2 t
    refine ⟨⟨x, hx⟩, Prod.ext (Subtype.ext (funext hc)) ht⟩
