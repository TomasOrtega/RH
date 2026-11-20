import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

namespace UpperTheory.HilbertUnitGroup

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {τ : K}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `w ∈ Submodule.span O {1, y} ↔ _`. Rewrite using `[Submodule.mem_span_pair]`. Simplify using `only [Algebra.smul_def, mul_one, eq_comm]`.
-/
private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ Submodule.span O {1, y} ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `mem_ord.1 hv`. Take `⟨a', b', rfl⟩` from `mem_ord.1 hw`. Use `mem_ord.2 ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul]`. Take the linear combination `(algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy`.
-/
private theorem ord_mul {y v w : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨a', b', rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
  simp only [map_add, map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy

/- English proof (translation)
Establish `one : (1 : Etau K τ) ∈ Ord O y` using `mem_ord.2 ⟨1, 0, by simp⟩`. Establish `key : ∀ v : (Etau K τ)ˣ, v ∈ Hu O y → ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y` using `fun v hv => by`. Establish `h1 : (1 : Etau K τ) ∈ PS.ml v (Ord O y)`. Rewrite using `[show PS.ml v (Ord O y) = Ord O y from hv]`. Conclude with `one`.

Simplify using `using PS.mem_ml.1 h1`. Use `⟨fun h => ⟨by simpa using key _ (inv_mem h), key _ h⟩, fun ⟨h1, h2⟩ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PS.ml u (Ord O y) = Ord O y`. Use extensionality with `w`. Rewrite using `[PS.mem_ml]`.

Use `⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩` and prove the remaining obligations. Simplify using `using ord_mul hy h1 hw`.
-/
private theorem mem_Hu {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c) {u : (Etau K τ)ˣ} :
    u ∈ Hu O y ↔ (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have one : (1 : Etau K τ) ∈ Ord O y := mem_ord.2 ⟨1, 0, by simp⟩
  have key : ∀ v : (Etau K τ)ˣ, v ∈ Hu O y → ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := fun v hv => by
    have h1 : (1 : Etau K τ) ∈ PS.ml v (Ord O y) := by
      rw [show PS.ml v (Ord O y) = Ord O y from hv]; exact one
    simpa using PS.mem_ml.1 h1
  refine ⟨fun h => ⟨by simpa using key _ (inv_mem h), key _ h⟩, fun ⟨h1, h2⟩ => ?_⟩
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  simpa using ord_mul hy h1 hw

/- English proof (translation)
Rewrite `h` using `[algebraMap_etau a, algebraMap_etau b, algebraMap_etau a', algebraMap_etau b']`. Establish `im_algebraMap_add_mul : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).im = q * y.im`. Introduce `p q`. Simplify using the standard rewrite rules. Establish `kre : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).re = p + q * y.re`.

Introduce `p q`. Simplify using the standard rewrite rules. Establish `him` using `congrArg QuadraticAlgebra.im h`. Establish `hre` using `congrArg QuadraticAlgebra.re h`. Rewrite `him` using `[im_algebraMap_add_mul, im_algebraMap_add_mul]`.

Rewrite `hre` using `[kre, kre]`. Establish `hb` using `mul_right_cancel₀ h0 him`. Rewrite `hre` using `[hb]`. Conclude with `⟨hinj (add_right_cancel hre), hinj hb⟩`.
-/
private theorem uniq (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {a b a' b' : O}
    (h : algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y =
      algebraMap O (Etau K τ) a' + algebraMap O (Etau K τ) b' * y) : a = a' ∧ b = b' := by
  rw [algebraMap_etau a, algebraMap_etau b, algebraMap_etau a', algebraMap_etau b'] at h
  have im_algebraMap_add_mul : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).im = q * y.im := by
    intro p q; simp
  have kre : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).re = p + q * y.re := by
    intro p q; simp
  have him := congrArg QuadraticAlgebra.im h
  have hre := congrArg QuadraticAlgebra.re h
  rw [im_algebraMap_add_mul, im_algebraMap_add_mul] at him
  rw [kre, kre] at hre
  have hb := mul_right_cancel₀ h0 him
  rw [hb] at hre
  exact ⟨hinj (add_right_cancel hre), hinj hb⟩

/- English proof (translation)
Take `⟨a', b', e'⟩` from `mem_ord.1 ((mem_Hu hy).1 hu).2`. Establish `h1 : algebraMap O (Etau K τ) (a * a' + b * b' * c) + algebraMap O (Etau K τ) (a * b' + a' * b) * y = algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) 0 * y`. Use `u.mul_inv` as an intermediate fact. Rewrite `this` using `[e, e']`. Simplify using `only [map_add, map_mul, map_one, map_zero]`.

Take the linear combination `this - (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy`. Establish `h2` using `(uniq hinj h0 h1).1`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one h2 with h3 | h3` into its components or cases. Conclude with `isUnit_of_mul_isUnit_left h3`. Conclude with `absurd (isUnit_of_mul_isUnit_right h3) hc`.
-/
private theorem isUnit_fst (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c : O}
    (hy : y * y = algebraMap O (Etau K τ) c) (hc : ¬ IsUnit c) {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) {a b : O}
    (e : (u : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y) : IsUnit a := by
  obtain ⟨a', b', e'⟩ := mem_ord.1 ((mem_Hu hy).1 hu).2
  have h1 : algebraMap O (Etau K τ) (a * a' + b * b' * c) + algebraMap O (Etau K τ) (a * b' + a' * b) * y =
      algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) 0 * y := by
    have := u.mul_inv
    rw [e, e'] at this
    simp only [map_add, map_mul, map_one, map_zero]
    linear_combination this - (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy
  have h2 := (uniq hinj h0 h1).1
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h2 with h3 | h3
  · exact isUnit_of_mul_isUnit_left h3
  · exact absurd (isUnit_of_mul_isUnit_right h3) hc

/- English proof (translation)
Establish `hcu : ¬ IsUnit c` using `fun h => hπ.not_isUnit (isUnit_of_dvd_unit hc h)`. Establish `hy' : (algebraMap O (Etau K τ) π * y) * (algebraMap O (Etau K τ) π * y) = algebraMap O (Etau K τ) (π * π * c)`. Simplify using `only [map_mul]`. Take the linear combination `(algebraMap O (Etau K τ) π * algebraMap O (Etau K τ) π) * hy`. Establish `hπ0 : IsLocalRing.residue O π = 0`.

Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `hπ.not_isUnit`. Establish `hc0 : IsLocalRing.residue O c = 0`. Take `⟨d, rfl⟩` from `hc`. Rewrite using `[map_mul, hπ0, zero_mul]`.

Establish `ex : ∀ u : Hu O y, ∃ p : O × O, ((u : (Etau K τ)ˣ) : Etau K τ) = algebraMap O (Etau K τ) p.1 + algebraMap O (Etau K τ) p.2 * y` using `fun u => by`. Take `⟨a, b, e⟩` from `mem_ord.1 ((mem_Hu hy).1 u.2).1`. Conclude with `⟨(a, b), e⟩`. Use `choose P hP using ex`. Set `g : Hu O y → IsLocalRing.ResidueField O` to `fun u => IsLocalRing.residue O (P u).2 / IsLocalRing.residue O (P u).1`.

Establish `gval : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y → g u = IsLocalRing.residue O b / IsLocalRing.residue O a` using `fun u a b e => by`. Take `⟨h1, h2⟩` from `uniq hinj h0 ((hP u).symm.trans e)`. Simplify using `only [g, h1, h2]`. Establish `resne : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y → IsLocalRing.residue O a ≠ 0` using `fun u a b e => ((isUnit_fst hinj h0 hy hcu u.2 e).map (IsLocalRing.residue O)).ne_zero`. Establish `gmul : ∀ u v : Hu O y, g (u * v) = g u + g v` using `fun u v => by`.

Establish `eu` using `hP u`. Establish `ev` using `hP v`. Establish `e : (((u * v : Hu O y) : (Etau K τ)ˣ) : Etau K τ) = algebraMap O (Etau K τ) ((P u).1 * (P v).1 + (P u).2 * (P v).2 * c) + algebraMap O (Etau K τ) ((P u).1 * (P v).2 + (P v).1 * (P u).2) * y`. Rewrite using `[Subgroup.coe_mul, Units.val_mul, eu, ev]`. Simplify using `only [map_add, map_mul]`.

Take the linear combination `(algebraMap O (Etau K τ) (P u).2 * algebraMap O (Etau K τ) (P v).2) * hy`. Establish `n1` using `resne u _ _ eu`. Establish `n2` using `resne v _ _ ev`. Rewrite using `[gval _ _ _ e, gval _ _ _ eu, gval _ _ _ ev]`. Simplify using `only [map_add, map_mul, hc0, mul_zero, add_zero]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Set `f : Hu O y →* Multiplicative (IsLocalRing.ResidueField O)` to `MonoidHom.mk' (fun u => Multiplicative.ofAdd (g u)) (fun u v => by rw [gmul, ofAdd_add])`. Establish `fval : ∀ u, f u = Multiplicative.ofAdd (g u)` using `fun _ => rfl`. Establish `down : ∀ u : Hu O y, f u = 1 → ((u : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O (algebraMap O (Etau K τ) π * y)` using `fun u hu => by`.

Establish `h1 : g u = 0` using `by simpa [fval] using hu`. Establish `e` using `hP u`. Rewrite `h1` using `[gval _ _ _ e, div_eq_zero_iff, or_iff_left (resne u _ _ e), IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton]`. Take `⟨d, hd⟩` from `h1`. Use `mem_ord.2 ⟨(P u).1, d, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, hd, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hker : f.ker = (Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y)`. Use extensionality with `u`. Rewrite using `[MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Hu hy']`.

Use `⟨fun hu => ⟨down u hu, ?_⟩, fun ⟨h1, _⟩ => ?_⟩` and prove the remaining obligations. Use `down u⁻¹ (by rw [map_inv, hu, inv_one])` as an intermediate fact. Simplify using `using this`. Take `⟨a, b, e⟩` from `mem_ord.1 h1`. Establish `e' : ((u : (Etau K τ)ˣ) : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) (b * π) * y`.

Rewrite using `[e, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[fval, gval _ _ _ e', map_mul, hπ0, mul_zero, zero_div, ofAdd_zero]`. Establish `hsurj : Function.Surjective f` using `fun r => by`. Take `⟨s, hs⟩` from `IsLocalRing.residue_surjective (Multiplicative.toAdd r)`.

Establish `hn : IsUnit (1 - s * s * c)`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one (a := 1 - s * s * c) (b := s * s * c) (by ring) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (isUnit_of_mul_isUnit_right h) hcu`. Take `⟨ν, hν⟩` from `hn`.

Establish `hν' : algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * (1 - algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) c) = 1`. Rewrite using `[← map_mul, ← map_mul, ← map_one (algebraMap O (Etau K τ)), ← map_sub, ← hν, ← map_mul, Units.inv_mul]`. Set `w : (Etau K τ)ˣ` to `{ val := algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) s * y inv := algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) + algebraMap O (Etau K τ) (-(((ν⁻¹ : Oˣ) : O) * s)) * y val_inv := by`. Simplify using `only [map_neg, map_mul, map_one]`. Take the linear combination `hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy`.

Use `inv_val := by`. Simplify using `only [map_neg, map_mul, map_one]`. Take the linear combination `hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy }`. Establish `hw : w ∈ Hu O y` using `(mem_Hu hy).2 ⟨mem_ord.2 ⟨1, s, rfl⟩, mem_ord.2 ⟨_, _, rfl⟩⟩`. Use `⟨⟨w, hw⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[fval, gval ⟨w, hw⟩ 1 s rfl, map_one, div_one, hs, ofAdd_toAdd]`. Establish `hr : f.range = ⊤` using `MonoidHom.range_eq_top.2 hsurj`. Express the relevant statement in the definitionally equal form `((Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y)).index = _`. Rewrite using `[← hker, Subgroup.index_ker, hr, Subgroup.card_top]`. Conclude with `Nat.card_congr Multiplicative.toAdd`.
-/
private theorem step (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c π : O}
    (hπ : Irreducible π) (hy : y * y = algebraMap O (Etau K τ) c) (hc : π ∣ c) :
    (Hu O (algebraMap O (Etau K τ) π * y)).relIndex (Hu O y) = Nat.card (IsLocalRing.ResidueField O) := by
  classical
  have hcu : ¬ IsUnit c := fun h => hπ.not_isUnit (isUnit_of_dvd_unit hc h)
  have hy' : (algebraMap O (Etau K τ) π * y) * (algebraMap O (Etau K τ) π * y) =
      algebraMap O (Etau K τ) (π * π * c) := by
    simp only [map_mul]; linear_combination (algebraMap O (Etau K τ) π * algebraMap O (Etau K τ) π) * hy
  have hπ0 : IsLocalRing.residue O π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
  have hc0 : IsLocalRing.residue O c = 0 := by
    obtain ⟨d, rfl⟩ := hc; rw [map_mul, hπ0, zero_mul]
  have ex : ∀ u : Hu O y, ∃ p : O × O, ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) p.1 + algebraMap O (Etau K τ) p.2 * y := fun u => by
    obtain ⟨a, b, e⟩ := mem_ord.1 ((mem_Hu hy).1 u.2).1
    exact ⟨(a, b), e⟩
  choose P hP using ex
  let g : Hu O y → IsLocalRing.ResidueField O := fun u =>
    IsLocalRing.residue O (P u).2 / IsLocalRing.residue O (P u).1
  have gval : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y →
      g u = IsLocalRing.residue O b / IsLocalRing.residue O a := fun u a b e => by
    obtain ⟨h1, h2⟩ := uniq hinj h0 ((hP u).symm.trans e)
    simp only [g, h1, h2]
  have resne : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y → IsLocalRing.residue O a ≠ 0 := fun u a b e =>
    ((isUnit_fst hinj h0 hy hcu u.2 e).map (IsLocalRing.residue O)).ne_zero
  have gmul : ∀ u v : Hu O y, g (u * v) = g u + g v := fun u v => by
    have eu := hP u
    have ev := hP v
    have e : (((u * v : Hu O y) : (Etau K τ)ˣ) : Etau K τ) =
        algebraMap O (Etau K τ) ((P u).1 * (P v).1 + (P u).2 * (P v).2 * c) +
          algebraMap O (Etau K τ) ((P u).1 * (P v).2 + (P v).1 * (P u).2) * y := by
      rw [Subgroup.coe_mul, Units.val_mul, eu, ev]
      simp only [map_add, map_mul]
      linear_combination (algebraMap O (Etau K τ) (P u).2 * algebraMap O (Etau K τ) (P v).2) * hy
    have n1 := resne u _ _ eu
    have n2 := resne v _ _ ev
    rw [gval _ _ _ e, gval _ _ _ eu, gval _ _ _ ev]
    simp only [map_add, map_mul, hc0, mul_zero, add_zero]
    field_simp
    ring
  let f : Hu O y →* Multiplicative (IsLocalRing.ResidueField O) :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (g u)) (fun u v => by rw [gmul, ofAdd_add])
  have fval : ∀ u, f u = Multiplicative.ofAdd (g u) := fun _ => rfl
  have down : ∀ u : Hu O y, f u = 1 → ((u : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O (algebraMap O (Etau K τ) π * y) := fun u hu => by
    have h1 : g u = 0 := by simpa [fval] using hu
    have e := hP u
    rw [gval _ _ _ e, div_eq_zero_iff, or_iff_left (resne u _ _ e), IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at h1
    obtain ⟨d, hd⟩ := h1
    refine mem_ord.2 ⟨(P u).1, d, ?_⟩
    rw [e, hd, map_mul]
    ring
  have hker : f.ker = (Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Hu hy']
    refine ⟨fun hu => ⟨down u hu, ?_⟩, fun ⟨h1, _⟩ => ?_⟩
    · have := down u⁻¹ (by rw [map_inv, hu, inv_one])
      simpa using this
    · obtain ⟨a, b, e⟩ := mem_ord.1 h1
      have e' : ((u : (Etau K τ)ˣ) : Etau K τ) =
          algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) (b * π) * y := by
        rw [e, map_mul]; ring
      rw [fval, gval _ _ _ e', map_mul, hπ0, mul_zero, zero_div, ofAdd_zero]
  have hsurj : Function.Surjective f := fun r => by
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (Multiplicative.toAdd r)
    have hn : IsUnit (1 - s * s * c) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := 1 - s * s * c) (b := s * s * c) (by ring) with h | h
      · exact h
      · exact absurd (isUnit_of_mul_isUnit_right h) hcu
    obtain ⟨ν, hν⟩ := hn
    have hν' : algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * (1 - algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) c) = 1 := by
      rw [← map_mul, ← map_mul, ← map_one (algebraMap O (Etau K τ)), ← map_sub, ← hν, ← map_mul, Units.inv_mul]
    let w : (Etau K τ)ˣ :=
      { val := algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) s * y
        inv := algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) + algebraMap O (Etau K τ) (-(((ν⁻¹ : Oˣ) : O) * s)) * y
        val_inv := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy
        inv_val := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy }
    have hw : w ∈ Hu O y := (mem_Hu hy).2 ⟨mem_ord.2 ⟨1, s, rfl⟩, mem_ord.2 ⟨_, _, rfl⟩⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [fval, gval ⟨w, hw⟩ 1 s rfl, map_one, div_one, hs, ofAdd_toAdd]
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  change ((Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y)).index = _
  rw [← hker, Subgroup.index_ker, hr, Subgroup.card_top]
  exact Nat.card_congr Multiplicative.toAdd

end UpperTheory.HilbertUnitGroup

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L _ π n e h x hC m hm`. Use `haveI := L.frac`. Establish `hinj : Function.Injective (algebraMap O K)` using `IsFractionRing.injective O K`. Establish `hπ` using `hC.irr`. Establish `hp : algebraMap O K (π ^ m) ≠ 0` using `fun h0 => pow_ne_zero m hπ.ne_zero (hinj (by rw [h0, map_zero]))`.

Establish `h0 : (yy π m x).im ≠ 0`. Rewrite using `[yy, im_smul, smul_eq_mul]`. Conclude with `mul_ne_zero hp hC.gen.im_ne`. Establish `hsm : ∀ k : ℕ, yy π k x = algebraMap O (Etau K τ) (π ^ k) * x` using `fun k => by`. Rewrite using `[yy, Algebra.smul_def, ← algebraMap_etau]`.

Establish `hy : yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * (e : O))`. Rewrite using `[hsm, map_mul, map_mul, ← hC.sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : π ∣ π ^ m * π ^ m * (e : O)` using `Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _) _`. Establish `e1 : yy π (m + 1) x = algebraMap O (Etau K τ) π * yy π m x`.

Rewrite using `[hsm, hsm, pow_succ, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `UpperTheory.HilbertUnitGroup.step hinj h0 hπ hy hc`.
-/
theorem UpperTheory.relIndex_stabilizer_succ_eq_card_residueField :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, 1 ≤ m → (Hu O (yy π (m + 1) x)).relIndex (Hu O (yy π m x)) = Nat.card (IsLocalRing.ResidueField O) := by
  intro O K _ _ _ _ _ Δ τ L _ π n e h x hC m hm
  haveI := L.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ := hC.irr
  have hp : algebraMap O K (π ^ m) ≠ 0 := fun h0 =>
    pow_ne_zero m hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have h0 : (yy π m x).im ≠ 0 := by
    rw [yy, im_smul, smul_eq_mul]
    exact mul_ne_zero hp hC.gen.im_ne
  have hsm : ∀ k : ℕ, yy π k x = algebraMap O (Etau K τ) (π ^ k) * x := fun k => by
    rw [yy, Algebra.smul_def, ← algebraMap_etau]
  have hy : yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * (e : O)) := by
    rw [hsm, map_mul, map_mul, ← hC.sq]; ring
  have hc : π ∣ π ^ m * π ^ m * (e : O) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _) _
  have e1 : yy π (m + 1) x = algebraMap O (Etau K τ) π * yy π m x := by
    rw [hsm, hsm, pow_succ, map_mul]; ring
  rw [e1]
  exact UpperTheory.HilbertUnitGroup.step hinj h0 hπ hy hc
