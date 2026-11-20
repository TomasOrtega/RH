import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

namespace UpperTheory.IdxOne

section
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private def el (x : Etau K τ) (a b : O) : Etau K τ :=
  algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * x

/- English proof (translation)
Simplify using `only [el, map_add, map_mul]`. Take the linear combination `(algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) d) * hx`.
-/
private theorem el_mul {x : Etau K τ} {e : O} (hx : x * x = algebraMap O (Etau K τ) e) (a b c d : O) :
    el x a b * el x c d = el x (a * c + e * b * d) (a * d + b * c) := by
  simp only [el, map_add, map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) d) * hx

/- English proof (translation)
Simplify using `[el]`.
-/
private theorem el_one (x : Etau K τ) : el x (1 : O) 0 = 1 := by simp [el]

/- English proof (translation)
Establish `hre` using `congrArg QuadraticAlgebra.re h`. Establish `him` using `congrArg QuadraticAlgebra.im h`. Simplify using `[el, algebraMap_etau] at hre him`. Establish `hbd : algebraMap O K b = algebraMap O K d` using `him.resolve_right hx`. Use `⟨hinj ?_, hinj hbd⟩` and prove the remaining obligations.

Rewrite `hre` using `[hbd]`. Conclude with `add_right_cancel hre`.
-/
private theorem el_inj (hinj : Function.Injective (algebraMap O K)) {x : Etau K τ} (hx : x.im ≠ 0)
    {a b c d : O} (h : el x a b = el x c d) : a = c ∧ b = d := by
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  simp [el, algebraMap_etau] at hre him
  have hbd : algebraMap O K b = algebraMap O K d := him.resolve_right hx
  refine ⟨hinj ?_, hinj hbd⟩
  rw [hbd] at hre
  exact add_right_cancel hre

/- English proof (translation)
Apply `Units.inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[hu, el_mul hx, ← el_one (O := O) x]`. Use `congr 1`. Take the linear combination `hi`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem inv_el {x : Etau K τ} {e : O} (hx : x * x = algebraMap O (Etau K τ) e)
    {u : (Etau K τ)ˣ} {a b i : O} (hu : (u : Etau K τ) = el x a b) (hi : (a ^ 2 - e * b ^ 2) * i = 1) :
    ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = el x (a * i) (-(b * i)) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [hu, el_mul hx, ← el_one (O := O) x]
  congr 1
  · linear_combination hi
  · ring

/- English proof (translation)
Simplify using `[yy, Algebra.smul_def, algebraMap_etau]`.
-/
private theorem yy_one (π : O) (x : Etau K τ) : yy π 1 x = algebraMap O (Etau K τ) π * x := by
  simp [yy, Algebra.smul_def, algebraMap_etau]

/- English proof (translation)
Simplify using `only [PK.Ord, SetLike.mem_coe, Submodule.mem_span_pair, yy_one, el]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, rfl⟩`. Conclude with `⟨a, b, by rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_mul]; ring⟩`. Introduce and unpack `⟨a, b, rfl⟩`.

Conclude with `⟨a, b, by rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_mul]; ring⟩`.
-/
private theorem mem_ord {π : O} {x w : Etau K τ} :
    w ∈ Ord O (yy π 1 x) ↔ ∃ a b : O, w = el x a (π * b) := by
  simp only [PK.Ord, SetLike.mem_coe, Submodule.mem_span_pair, yy_one, el]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_mul]; ring⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_mul]; ring⟩

/- English proof (translation)
Introduce and unpack `_ ⟨w, hw, rfl⟩`. Take `⟨c, d, rfl⟩` from `mem_ord.mp hw`. Rewrite using `[hv]`. Simplify using `only`. Rewrite using `[el_mul hx]`.

Use `mem_ord.mpr ⟨a * c + e * (π * q) * (π * d), a * d + q * c, ?_⟩` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ml_sub {π e : O} {x : Etau K τ} (hx : x * x = algebraMap O (Etau K τ) e)
    {v : (Etau K τ)ˣ} {a q : O} (hv : (v : Etau K τ) = el x a (π * q)) :
    PS.ml v (Ord O (yy π 1 x)) ⊆ Ord O (yy π 1 x) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨c, d, rfl⟩ := mem_ord.mp hw
  rw [hv]
  dsimp only
  rw [el_mul hx]
  refine mem_ord.mpr ⟨a * c + e * (π * q) * (π * d), a * d + q * c, ?_⟩
  congr 1
  ring

/- English proof (translation)
Establish `h1 : (1 : Etau K τ) ∈ Ord O (yy π 1 x)` using `mem_ord.mpr ⟨1, 0, by rw [mul_zero, el_one]⟩`. Use `show PS.ml u (Ord O (yy π 1 x)) = Ord O (yy π 1 x) ↔ π ∣ b`. Prove the components needed by the constructor for the conclusion. Introduce `hm`. Establish `hu1 : (u : Etau K τ) ∈ Ord O (yy π 1 x)`.

Rewrite using `[← hm]`. Conclude with `⟨1, h1, mul_one _⟩`. Take `⟨c, d, hcd⟩` from `mem_ord.mp hu1`. Rewrite `hcd` using `[hu]`. Conclude with `⟨d, (el_inj hinj h0 hcd).2⟩`.

Introduce and unpack `⟨q, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i : O, (a ^ 2 - e * (π * q) ^ 2) * i = 1 := by`. Take `⟨w, hw⟩` from `hN`. Conclude with `⟨↑w⁻¹, by rw [← hw]; exact w.mul_inv⟩`. Establish `hinv` using `inv_el hx hu hi`.

Apply `Set.Subset.antisymm (ml_sub hx hu)` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[PS.mem_ml]`. Establish `hsub` using `ml_sub (π := π) (q := -(q * i)) hx (v := u⁻¹) (a := a * i) (by rw [hinv]; congr 1; ring)`. Conclude with `hsub ⟨w, hw, rfl⟩`.
-/
private theorem hu_iff (hinj : Function.Injective (algebraMap O K)) {π e : O} {x : Etau K τ} (h0 : x.im ≠ 0)
    (hx : x * x = algebraMap O (Etau K τ) e) {u : (Etau K τ)ˣ} {a b : O} (hu : (u : Etau K τ) = el x a b)
    (hN : IsUnit (a ^ 2 - e * b ^ 2)) : u ∈ Hu O (yy π 1 x) ↔ π ∣ b := by
  have h1 : (1 : Etau K τ) ∈ Ord O (yy π 1 x) := mem_ord.mpr ⟨1, 0, by rw [mul_zero, el_one]⟩
  show PS.ml u (Ord O (yy π 1 x)) = Ord O (yy π 1 x) ↔ π ∣ b
  constructor
  · intro hm
    have hu1 : (u : Etau K τ) ∈ Ord O (yy π 1 x) := by
      rw [← hm]
      exact ⟨1, h1, mul_one _⟩
    obtain ⟨c, d, hcd⟩ := mem_ord.mp hu1
    rw [hu] at hcd
    exact ⟨d, (el_inj hinj h0 hcd).2⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i : O, (a ^ 2 - e * (π * q) ^ 2) * i = 1 := by
      obtain ⟨w, hw⟩ := hN
      exact ⟨↑w⁻¹, by rw [← hw]; exact w.mul_inv⟩
    have hinv := inv_el hx hu hi
    apply Set.Subset.antisymm (ml_sub hx hu)
    intro w hw
    rw [PS.mem_ml]
    have hsub := ml_sub (π := π) (q := -(q * i)) hx (v := u⁻¹) (a := a * i)
      (by rw [hinv]; congr 1; ring)
    exact hsub ⟨w, hw, rfl⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i : O, (a ^ 2 - e * b ^ 2) * i = 1 := by`. Take `⟨w, hw⟩` from `hNu`. Conclude with `⟨↑w⁻¹, by rw [← hw]; exact w.mul_inv⟩`. Establish `hiu : IsUnit i` using `⟨⟨i, a ^ 2 - e * b ^ 2, by rw [mul_comm]; exact hi, hi⟩, rfl⟩`. Establish `hprod : ((u⁻¹ * v : (Etau K τ)ˣ) : Etau K τ) = el x (i * (a * c - e * b * d)) (i * (a * d - b * c))`.

Rewrite using `[Units.val_mul, inv_el hx hu hi, hv, el_mul hx]`. Apply the tactic sequence `congr 1 <;> ring`. Establish `hN : IsUnit ((i * (a * c - e * b * d)) ^ 2 - e * (i * (a * d - b * c)) ^ 2)`. Establish `hid : (i * (a * c - e * b * d)) ^ 2 - e * (i * (a * d - b * c)) ^ 2 = i ^ 2 * ((a ^ 2 - e * b ^ 2) * (c ^ 2 - e * d ^ 2))` using `by ring`. Rewrite using `[hid]`.

Conclude with `(hiu.pow 2).mul (hNu.mul hNv)`. Rewrite using `[hu_iff hinj h0 hx hprod hN]`. Conclude with `hiu.dvd_mul_left`.
-/
private theorem rel_iff (hinj : Function.Injective (algebraMap O K)) {π e : O} {x : Etau K τ} (h0 : x.im ≠ 0)
    (hx : x * x = algebraMap O (Etau K τ) e) {u v : (Etau K τ)ˣ} {a b c d : O}
    (hu : (u : Etau K τ) = el x a b) (hv : (v : Etau K τ) = el x c d)
    (hNu : IsUnit (a ^ 2 - e * b ^ 2)) (hNv : IsUnit (c ^ 2 - e * d ^ 2)) :
    u⁻¹ * v ∈ Hu O (yy π 1 x) ↔ π ∣ a * d - b * c := by
  obtain ⟨i, hi⟩ : ∃ i : O, (a ^ 2 - e * b ^ 2) * i = 1 := by
    obtain ⟨w, hw⟩ := hNu
    exact ⟨↑w⁻¹, by rw [← hw]; exact w.mul_inv⟩
  have hiu : IsUnit i := ⟨⟨i, a ^ 2 - e * b ^ 2, by rw [mul_comm]; exact hi, hi⟩, rfl⟩
  have hprod : ((u⁻¹ * v : (Etau K τ)ˣ) : Etau K τ)
      = el x (i * (a * c - e * b * d)) (i * (a * d - b * c)) := by
    rw [Units.val_mul, inv_el hx hu hi, hv, el_mul hx]
    congr 1 <;> ring
  have hN : IsUnit ((i * (a * c - e * b * d)) ^ 2 - e * (i * (a * d - b * c)) ^ 2) := by
    have hid : (i * (a * c - e * b * d)) ^ 2 - e * (i * (a * d - b * c)) ^ 2
        = i ^ 2 * ((a ^ 2 - e * b ^ 2) * (c ^ 2 - e * d ^ 2)) := by ring
    rw [hid]
    exact (hiu.pow 2).mul (hNu.mul hNv)
  rw [hu_iff hinj h0 hx hprod hN]
  exact hiu.dvd_mul_left

end

/- English proof (translation)
Set `F : G ⧸ H → Set.range f` to `fun q => Quotient.liftOn' q (fun u => (⟨f u, u, rfl⟩ : Set.range f)) (fun u v huv => Subtype.ext ((hf u v).mpr (QuotientGroup.leftRel_apply.mp huv)))`. Establish `hF : Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce `p q hpq`. Take `⟨u, rfl⟩` from `QuotientGroup.mk_surjective p`.

Take `⟨v, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `QuotientGroup.eq.mpr ((hf u v).mp (congrArg Subtype.val hpq))`. Introduce and unpack `⟨t, u, rfl⟩`. Conclude with `⟨QuotientGroup.mk u, rfl⟩`. Conclude with `Nat.card_congr (Equiv.ofBijective F hF)`.
-/
private theorem index_of_fibres {G T : Type} [Group G] (H : Subgroup G) (f : G → T)
    (hf : ∀ u v, f u = f v ↔ u⁻¹ * v ∈ H) : H.index = Nat.card (Set.range f) := by
  classical
  let F : G ⧸ H → Set.range f := fun q =>
    Quotient.liftOn' q (fun u => (⟨f u, u, rfl⟩ : Set.range f))
      (fun u v huv => Subtype.ext ((hf u v).mpr (QuotientGroup.leftRel_apply.mp huv)))
  have hF : Function.Bijective F := by
    constructor
    · intro p q hpq
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
      exact QuotientGroup.eq.mpr ((hf u v).mp (congrArg Subtype.val hpq))
    · rintro ⟨t, u, rfl⟩
      exact ⟨QuotientGroup.mk u, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective F hF)

private noncomputable def pt {k : Type} [Field k] (α β : k) : Option k := by
  classical exact if α = 0 then none else some (β / α)

/- English proof (translation)
Unfold `pt`. Apply the tactic sequence `by_cases ha : α = 0 <;> by_cases hc : γ = 0`. Simplify using `[ha, hc]`. Establish `hb : β ≠ 0` using `h1.resolve_left (not_not.mpr ha)`. Simplify using `[ha, hc, hb]`.

Establish `hd : δ ≠ 0` using `h2.resolve_left (not_not.mpr hc)`. Simplify using `[ha, hc, hd]`. Simplify using `only [ha, hc, if_false, Option.some.injEq]`. Rewrite using `[div_eq_div_iff ha hc]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination -h`.
-/
private theorem pt_eq {k : Type} [Field k] {α β γ δ : k} (h1 : α ≠ 0 ∨ β ≠ 0) (h2 : γ ≠ 0 ∨ δ ≠ 0) :
    pt α β = pt γ δ ↔ α * δ - β * γ = 0 := by
  unfold pt
  by_cases ha : α = 0 <;> by_cases hc : γ = 0
  · simp [ha, hc]
  · have hb : β ≠ 0 := h1.resolve_left (not_not.mpr ha)
    simp [ha, hc, hb]
  · have hd : δ ≠ 0 := h2.resolve_left (not_not.mpr hc)
    simp [ha, hc, hd]
  · simp only [ha, hc, if_false, Option.some.injEq]
    rw [div_eq_div_iff ha hc]
    constructor <;> intro h <;> linear_combination -h

section
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O K)` using `by haveI := L.frac`. Conclude with `IsFractionRing.injective O K`. Establish `hx` using `c.sq`. Establish `h0 : x.im ≠ 0` using `c.gen.im_ne`. Establish `hu' : IsIntegral O (u : Etau K τ) ∧ IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)` using `hu`.

Take `⟨a, b, hab⟩` from `(Gen1.int_iff L c.gen (u : Etau K τ)).mp hu'.1`. Take `⟨a', b', hab'⟩` from `(Gen1.int_iff L c.gen ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)).mp hu'.2`. Establish `hu1 : (u : Etau K τ) = el x a b` using `hab`. Establish `hu2 : ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = el x a' b'` using `hab'`. Use `⟨a, b, hu1, ?_⟩` and prove the remaining obligations.

Establish `hprod : el x a b * el x a' b' = el x (1 : O) 0`. Rewrite using `[el_one, ← hu1, ← hu2, Units.mul_inv]`. Rewrite `hprod` using `[el_mul hx]`. Take `⟨h1, h2⟩` from `el_inj hinj h0 hprod`. Use `IsUnit.of_mul_eq_one (a' ^ 2 - (e : O) * b' ^ 2) ?_` and prove the remaining obligations.

Take the linear combination `(a * a' + (e : O) * b * b' + 1) * h1 - (e : O) * (a * b' + b * a') * h2`.
-/
private theorem gu_coords (L : IsLoc O Δ) {π : O} {n : ℕ} {e : Oˣ} {h : O} {x : Etau K τ} (c : Cond π n e h x)
    {u : (Etau K τ)ˣ} (hu : u ∈ Gu O τ) :
    ∃ a b : O, (u : Etau K τ) = el x a b ∧ IsUnit (a ^ 2 - (e : O) * b ^ 2) := by
  have hinj : Function.Injective (algebraMap O K) := by
    haveI := L.frac
    exact IsFractionRing.injective O K
  have hx := c.sq
  have h0 : x.im ≠ 0 := c.gen.im_ne
  have hu' : IsIntegral O (u : Etau K τ) ∧ IsIntegral O ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) := hu
  obtain ⟨a, b, hab⟩ := (Gen1.int_iff L c.gen (u : Etau K τ)).mp hu'.1
  obtain ⟨a', b', hab'⟩ := (Gen1.int_iff L c.gen ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)).mp hu'.2
  have hu1 : (u : Etau K τ) = el x a b := hab
  have hu2 : ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = el x a' b' := hab'
  refine ⟨a, b, hu1, ?_⟩
  have hprod : el x a b * el x a' b' = el x (1 : O) 0 := by
    rw [el_one, ← hu1, ← hu2, Units.mul_inv]
  rw [el_mul hx] at hprod
  obtain ⟨h1, h2⟩ := el_inj hinj h0 hprod
  refine IsUnit.of_mul_eq_one (a' ^ 2 - (e : O) * b' ^ 2) ?_
  linear_combination (a * a' + (e : O) * b * b' + 1) * h1 - (e : O) * (a * b' + b * a') * h2

/- English proof (translation)
Establish `hx` using `c.sq`. Take `⟨i, hi⟩` from `hN.exists_right_inv`. Establish `e1 : a * (a * i) + (e : O) * b * -(b * i) = 1` using `by linear_combination hi`. Establish `e2 : a * -(b * i) + b * (a * i) = 0` using `by ring`. Establish `h1 : el x a b * el x (a * i) (-(b * i)) = 1`.

Rewrite using `[el_mul hx, e1, e2, el_one]`. Set `v : (Etau K τ)ˣ` to `⟨el x a b, el x (a * i) (-(b * i)), h1, by rw [mul_comm]; exact h1⟩`. Establish `hint : ∀ p q : O, IsIntegral O (el x p q)` using `fun p q => (Gen1.int_iff L c.gen _).mpr ⟨p, q, rfl⟩`. Conclude with `⟨⟨v, hint a b, hint (a * i) (-(b * i))⟩, rfl⟩`.
-/
private theorem mk_gu (L : IsLoc O Δ) {π : O} {n : ℕ} {e : Oˣ} {h : O} {x : Etau K τ} (c : Cond π n e h x)
    (a b : O) (hN : IsUnit (a ^ 2 - (e : O) * b ^ 2)) :
    ∃ g : Gu O τ, ((g : (Etau K τ)ˣ) : Etau K τ) = el x a b := by
  have hx := c.sq
  obtain ⟨i, hi⟩ := hN.exists_right_inv
  have e1 : a * (a * i) + (e : O) * b * -(b * i) = 1 := by linear_combination hi
  have e2 : a * -(b * i) + b * (a * i) = 0 := by ring
  have h1 : el x a b * el x (a * i) (-(b * i)) = 1 := by
    rw [el_mul hx, e1, e2, el_one]
  let v : (Etau K τ)ˣ := ⟨el x a b, el x (a * i) (-(b * i)), h1, by rw [mul_comm]; exact h1⟩
  have hint : ∀ p q : O, IsIntegral O (el x p q) := fun p q => (Gen1.int_iff L c.gen _).mpr ⟨p, q, rfl⟩
  exact ⟨⟨v, hint a b, hint (a * i) (-(b * i))⟩, rfl⟩

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O K)` using `by haveI := L.frac`. Conclude with `IsFractionRing.injective O K`. Establish `h0 : x.im ≠ 0` using `c.gen.im_ne`. Establish `hx` using `c.sq`. Establish `hmax : IsLocalRing.maximalIdeal O = Ideal.span {π}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp c.irr`.

Establish `hres0 : ∀ z : O, IsLocalRing.residue O z = 0 ↔ π ∣ z`. Introduce `z`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]`. Establish `hunit : ∀ z : O, IsUnit z ↔ IsLocalRing.residue O z ≠ 0`. Introduce `z`.

Rewrite using `[Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Establish `hc : ∀ g : Gu O τ, ∃ a b : O, ((g : (Etau K τ)ˣ) : Etau K τ) = el x a b ∧ IsUnit (a ^ 2 - (e : O) * b ^ 2)` using `fun g => gu_coords L c g.2`. Use `choose A B hAB hN using hc`. Set `r` to `IsLocalRing.residue O`. Set `f : Gu O τ → Option (IsLocalRing.ResidueField O)` to `fun g => pt (r (A g)) (r (B g))`.

Establish `hN' : ∀ g, r (A g) ^ 2 - r (e : O) * r (B g) ^ 2 ≠ 0`. Introduce `g`. Use `(hunit _).mp (hN g)` as an intermediate fact. Simplify `this` using `[r, map_sub, map_mul, map_pow]`. Establish `hnz : ∀ g, r (A g) ≠ 0 ∨ r (B g) ≠ 0`.

Introduce `g`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hN' g` to reduce the goal to its premises. Rewrite using `[hcon.1, hcon.2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hf : ∀ u v : Gu O τ, f u = f v ↔ u⁻¹ * v ∈ (Hu O (yy π 1 x)).subgroupOf (Gu O τ)`. Introduce `u v`. Rewrite using `[Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, rel_iff hinj h0 hx (hAB u) (hAB v) (hN u) (hN v), ← hres0]`. Use `show pt _ _ = pt _ _ ↔ _`.

Rewrite using `[pt_eq (hnz u) (hnz v)]`. Simplify using `only [r, map_sub, map_mul]`. Establish `hidx : (Hu O (yy π 1 x)).relIndex (Gu O τ) = Nat.card (Set.range f)` using `index_of_fibres _ f hf`. Rewrite using `[hidx]`. Establish `hrange : Set.range f = insert none (Option.some '' {t : IsLocalRing.ResidueField O | t ^ 2 * r (e : O) ≠ 1})`.

Use extensionality with `w`. Simplify using `only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Distinguish the cases in `ha : r (A g) = 0`.

Use `left`. Simplify using `[f, pt, ha]`. Use `right`. Use `⟨r (B g) / r (A g), ?_, ?_⟩` and prove the remaining obligations. Introduce `heq`.

Apply `hN' g` to reduce the goal to its premises. Clear denominators, using `at heq` for the nonvanishing conditions. Take the linear combination `-heq`. Simplify using `[f, pt, ha]`. Introduce and unpack `(rfl | ⟨t, ht, rfl⟩)`.

Establish `hN0 : IsUnit ((0 : O) ^ 2 - (e : O) * 1 ^ 2)` using `by simp`. Take `⟨g, hg⟩` from `mk_gu L c 0 1 hN0`. Use `⟨g, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `el_inj hinj h0 ((hAB g).symm.trans hg)`. Simplify using `[f, pt, h1]`.

Take `⟨t0, rfl⟩` from `IsLocalRing.residue_surjective t`. Establish `hN1 : IsUnit ((1 : O) ^ 2 - (e : O) * t0 ^ 2)`. Rewrite using `[hunit, map_sub, map_mul, map_pow, map_pow, map_one]`. Introduce `h`. Apply `ht` to reduce the goal to its premises.

Take the linear combination `-h`. Take `⟨g, hg⟩` from `mk_gu L c 1 t0 hN1`. Use `⟨g, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `el_inj hinj h0 ((hAB g).symm.trans hg)`. Simplify using `[f, pt, h1, h2, r]`.

Rewrite using `[hrange]`. Use `haveI := L.fin`. Rewrite using `[Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (by simp) (Set.toFinite _), Set.ncard_image_of_injective _ (Option.some_injective _), add_comm]`.
-/
private theorem count (L : IsLoc O Δ) {π : O} {n : ℕ} {e : Oˣ} {h : O} {x : Etau K τ} (c : Cond π n e h x) :
    (Hu O (yy π 1 x)).relIndex (Gu O τ) =
      1 + {t : IsLocalRing.ResidueField O | t ^ 2 * IsLocalRing.residue O (e : O) ≠ 1}.ncard := by
  classical
  have hinj : Function.Injective (algebraMap O K) := by
    haveI := L.frac
    exact IsFractionRing.injective O K
  have h0 : x.im ≠ 0 := c.gen.im_ne
  have hx := c.sq
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp c.irr
  have hres0 : ∀ z : O, IsLocalRing.residue O z = 0 ↔ π ∣ z := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]
  have hunit : ∀ z : O, IsUnit z ↔ IsLocalRing.residue O z ≠ 0 := by
    intro z
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hc : ∀ g : Gu O τ, ∃ a b : O, ((g : (Etau K τ)ˣ) : Etau K τ) = el x a b ∧
      IsUnit (a ^ 2 - (e : O) * b ^ 2) := fun g => gu_coords L c g.2
  choose A B hAB hN using hc
  let r := IsLocalRing.residue O
  let f : Gu O τ → Option (IsLocalRing.ResidueField O) := fun g => pt (r (A g)) (r (B g))
  have hN' : ∀ g, r (A g) ^ 2 - r (e : O) * r (B g) ^ 2 ≠ 0 := by
    intro g
    have := (hunit _).mp (hN g)
    simpa [r, map_sub, map_mul, map_pow] using this
  have hnz : ∀ g, r (A g) ≠ 0 ∨ r (B g) ≠ 0 := by
    intro g
    by_contra hcon
    push_neg at hcon
    apply hN' g
    rw [hcon.1, hcon.2]
    ring
  have hf : ∀ u v : Gu O τ, f u = f v ↔ u⁻¹ * v ∈ (Hu O (yy π 1 x)).subgroupOf (Gu O τ) := by
    intro u v
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      rel_iff hinj h0 hx (hAB u) (hAB v) (hN u) (hN v), ← hres0]
    show pt _ _ = pt _ _ ↔ _
    rw [pt_eq (hnz u) (hnz v)]
    simp only [r, map_sub, map_mul]
  have hidx : (Hu O (yy π 1 x)).relIndex (Gu O τ) = Nat.card (Set.range f) :=
    index_of_fibres _ f hf
  rw [hidx]
  have hrange : Set.range f =
      insert none (Option.some '' {t : IsLocalRing.ResidueField O | t ^ 2 * r (e : O) ≠ 1}) := by
    ext w
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, rfl⟩
      by_cases ha : r (A g) = 0
      · left
        simp [f, pt, ha]
      · right
        refine ⟨r (B g) / r (A g), ?_, ?_⟩
        · intro heq
          apply hN' g
          field_simp at heq
          linear_combination -heq
        · simp [f, pt, ha]
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · have hN0 : IsUnit ((0 : O) ^ 2 - (e : O) * 1 ^ 2) := by simp
        obtain ⟨g, hg⟩ := mk_gu L c 0 1 hN0
        refine ⟨g, ?_⟩
        obtain ⟨h1, h2⟩ := el_inj hinj h0 ((hAB g).symm.trans hg)
        simp [f, pt, h1]
      · obtain ⟨t0, rfl⟩ := IsLocalRing.residue_surjective t
        have hN1 : IsUnit ((1 : O) ^ 2 - (e : O) * t0 ^ 2) := by
          rw [hunit, map_sub, map_mul, map_pow, map_pow, map_one]
          intro h
          apply ht
          linear_combination -h
        obtain ⟨g, hg⟩ := mk_gu L c 1 t0 hN1
        refine ⟨g, ?_⟩
        obtain ⟨h1, h2⟩ := el_inj hinj h0 ((hAB g).symm.trans hg)
        simp [f, pt, h1, h2, r]
  rw [hrange]
  haveI := L.fin
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem (by simp) (Set.toFinite _),
    Set.ncard_image_of_injective _ (Option.some_injective _), add_comm]

end

end UpperTheory.IdxOne

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hτ π n e h x c`. Establish `hc` using `UpperTheory.IdxOne.count L c`. Use `haveI := L.fin`. Establish `he0 : IsLocalRing.residue O (e : O) ≠ 0`. Rewrite using `[Ne, IsLocalRing.residue_eq_zero_iff]`.

Conclude with `fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm e.isUnit`. Prove the components needed by the constructor for the conclusion. Introduce `hns`. Rewrite using `[hc]`. Establish `hS : {t : IsLocalRing.ResidueField O | t ^ 2 * IsLocalRing.residue O (e : O) ≠ 1} = Set.univ`.

Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, Set.mem_univ, iff_true]`. Introduce `ht`. Apply `hns` to reduce the goal to its premises. Establish `ht0 : t ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at ht`. Take `⟨r₀, hr₀⟩` from `IsLocalRing.residue_surjective t⁻¹`. Establish `hr₀u : IsUnit r₀`. Assume the negation of the conclusion as `hnu`.

Establish `: IsLocalRing.residue O r₀ = 0` using `(IsLocalRing.residue_eq_zero_iff r₀).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)`. Rewrite `this` using `[hr₀]`. Conclude with `inv_ne_zero ht0 this`. Establish `hinv : t⁻¹ ^ 2 * t ^ 2 = 1`. Rewrite using `[← mul_pow, inv_mul_cancel₀ ht0, one_pow]`.

Take `⟨r, hr, -⟩` from `UpperTheory.V.Z.Sym.Loc.sqrtO O K Δ L (e : O) r₀ hr₀u (by`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hr₀]`. Take the linear combination `t⁻¹ ^ 2 * ht - (IsLocalRing.residue O (e : O)) * hinv)`. Conclude with `⟨r, by rw [← hr, sq]⟩`. Rewrite using `[hS, Set.ncard_univ, add_comm]`.

Introduce and unpack `⟨r, hr⟩`. Rewrite using `[hc]`. Use `set a := IsLocalRing.residue O r with ha`. Establish `hea : IsLocalRing.residue O (e : O) = a * a` using `by rw [hr, map_mul]`. Establish `ha0 : a ≠ 0`.

Introduce `h0`. Apply `he0` to reduce the goal to its premises. Rewrite using `[hea, h0, zero_mul]`. Establish `h2 : (2 : IsLocalRing.ResidueField O) ≠ 0`. Establish `h2' : IsLocalRing.residue O (2 : O) ≠ 0`.

Rewrite using `[Ne, IsLocalRing.residue_eq_zero_iff]`. Conclude with `fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm L.two`. Rewrite `h2'` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `hne : a⁻¹ ≠ -a⁻¹`. Introduce `hh`.

Establish `: (2 : IsLocalRing.ResidueField O) * a⁻¹ = 0` using `by linear_combination hh`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `h2 h`. Conclude with `inv_ne_zero ha0 h`. Establish `hC : {t : IsLocalRing.ResidueField O | t ^ 2 * IsLocalRing.residue O (e : O) ≠ 1}ᶜ = {a⁻¹, -a⁻¹}`.

Use extensionality with `t`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not, Set.mem_insert_iff, Set.mem_singleton_iff, hea]`. Establish `haa : a * a⁻¹ = 1` using `mul_inv_cancel₀ ha0`. Prove the components needed by the constructor for the conclusion. Introduce `ht`.

Establish `: (t - a⁻¹) * (t + a⁻¹) = 0`. Take the linear combination `a⁻¹ * a⁻¹ * ht - t ^ 2 * (a * a⁻¹ + 1) * haa`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Use `left`. Take the linear combination `h`.

Use `right`. Take the linear combination `h`. Introduce and unpack `(rfl | rfl)`. Take the linear combination `(a * a⁻¹ + 1) * haa`. Take the linear combination `(a * a⁻¹ + 1) * haa`.

Establish `hsum` using `Set.ncard_add_ncard_compl {t : IsLocalRing.ResidueField O | t ^ 2 * IsLocalRing.residue O (e : O) ≠ 1}`. Rewrite `hsum` using `[hC, Set.ncard_pair hne]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.relIndex_stabilizer_level_one_of_isSquare_unit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (¬ IsSquare (e : O) → (Hu O (yy π 1 x)).relIndex (Gu O τ) = Nat.card (IsLocalRing.ResidueField O) + 1) ∧ (IsSquare (e : O) → (Hu O (yy π 1 x)).relIndex (Gu O τ) + 1 = Nat.card (IsLocalRing.ResidueField O)) := by
  intro O K _ _ _ _ _ Δ τ L hτ π n e h x c
  have hc := UpperTheory.IdxOne.count L c
  haveI := L.fin
  have he0 : IsLocalRing.residue O (e : O) ≠ 0 := by
    rw [Ne, IsLocalRing.residue_eq_zero_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm e.isUnit
  constructor
  · intro hns
    rw [hc]
    have hS : {t : IsLocalRing.ResidueField O | t ^ 2 * IsLocalRing.residue O (e : O) ≠ 1} = Set.univ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro ht
      apply hns
      have ht0 : t ≠ 0 := by
        rintro rfl
        simp at ht
      obtain ⟨r₀, hr₀⟩ := IsLocalRing.residue_surjective t⁻¹
      have hr₀u : IsUnit r₀ := by
        by_contra hnu
        have : IsLocalRing.residue O r₀ = 0 :=
          (IsLocalRing.residue_eq_zero_iff r₀).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
        rw [hr₀] at this
        exact inv_ne_zero ht0 this
      have hinv : t⁻¹ ^ 2 * t ^ 2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ ht0, one_pow]
      obtain ⟨r, hr, -⟩ := UpperTheory.V.Z.Sym.Loc.sqrtO O K Δ L (e : O) r₀ hr₀u (by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hr₀]
        linear_combination t⁻¹ ^ 2 * ht - (IsLocalRing.residue O (e : O)) * hinv)
      exact ⟨r, by rw [← hr, sq]⟩
    rw [hS, Set.ncard_univ, add_comm]
  · rintro ⟨r, hr⟩
    rw [hc]
    set a := IsLocalRing.residue O r with ha
    have hea : IsLocalRing.residue O (e : O) = a * a := by rw [hr, map_mul]
    have ha0 : a ≠ 0 := by
      intro h0
      apply he0
      rw [hea, h0, zero_mul]
    have h2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
      have h2' : IsLocalRing.residue O (2 : O) ≠ 0 := by
        rw [Ne, IsLocalRing.residue_eq_zero_iff]
        exact fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm L.two
      rwa [map_ofNat] at h2'
    have hne : a⁻¹ ≠ -a⁻¹ := by
      intro hh
      have : (2 : IsLocalRing.ResidueField O) * a⁻¹ = 0 := by linear_combination hh
      rcases mul_eq_zero.mp this with h | h
      · exact h2 h
      · exact inv_ne_zero ha0 h
    have hC : {t : IsLocalRing.ResidueField O | t ^ 2 * IsLocalRing.residue O (e : O) ≠ 1}ᶜ = {a⁻¹, -a⁻¹} := by
      ext t
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not, Set.mem_insert_iff, Set.mem_singleton_iff, hea]
      have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
      constructor
      · intro ht
        have : (t - a⁻¹) * (t + a⁻¹) = 0 := by
          linear_combination a⁻¹ * a⁻¹ * ht - t ^ 2 * (a * a⁻¹ + 1) * haa
        rcases mul_eq_zero.mp this with h | h
        · left; linear_combination h
        · right; linear_combination h
      · rintro (rfl | rfl)
        · linear_combination (a * a⁻¹ + 1) * haa
        · linear_combination (a * a⁻¹ + 1) * haa
    have hsum := Set.ncard_add_ncard_compl
      {t : IsLocalRing.ResidueField O | t ^ 2 * IsLocalRing.residue O (e : O) ≠ 1}
    rw [hC, Set.ncard_pair hne] at hsum
    omega
