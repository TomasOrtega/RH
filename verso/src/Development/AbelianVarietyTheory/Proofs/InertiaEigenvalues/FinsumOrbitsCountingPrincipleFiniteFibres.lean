import Mathlib

open Polynomial

namespace GlobalTheory.OrbitCounting

/- English proof (translation)
Use extensionality with `h`. Simplify using `only [MulAction.mem_stabilizer_iff]`. Rewrite using `[← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]`.
-/
theorem stabilizer_smul_eq {G X : Type} [CommGroup G] [MulAction G X] (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]

/- English proof (translation)
Establish `hset : {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} = MulAction.orbit (MulAction.stabilizer G (π x0)) x0`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, g, rfl⟩`. Use `⟨⟨g, ?_⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[MulAction.mem_stabilizer_iff, ← hπ]`. Conclude with `hx`. Introduce and unpack `⟨⟨g, hg⟩, rfl⟩`. Use `⟨?_, ⟨g, rfl⟩⟩` and prove the remaining obligations. Use `show π (g • x0) = π x0`.

Rewrite using `[hπ]`. Conclude with `hg`. Rewrite using `[hset, Subgroup.relIndex, ← MulAction.index_stabilizer]`. Use `congr 1`.
-/
theorem ncard_fibre_inter_orbit {G X Y : Type} [CommGroup G] [MulAction G X] [MulAction G Y]
    (π : X → Y) (hπ : ∀ (g : G) (x : X), π (g • x) = g • π x) (x0 : X) :
    {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0}.ncard =
      (MulAction.stabilizer G x0).relIndex (MulAction.stabilizer G (π x0)) := by
  have hset : {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} =
      MulAction.orbit (MulAction.stabilizer G (π x0)) x0 := by
    ext x; constructor
    · rintro ⟨hx, g, rfl⟩
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hπ]; exact hx
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨?_, ⟨g, rfl⟩⟩
      show π (g • x0) = π x0
      rw [hπ]; exact hg
  rw [hset, Subgroup.relIndex, ← MulAction.index_stabilizer]
  congr 1

/- English proof (translation)
Introduce `G X Y _ _ _ Gc π hπ hfin hstab hY w hw`. Establish `hmem : ∀ a b : X, a ∈ MulAction.orbit G b → π a ∈ MulAction.orbit G (π b)`. Introduce and unpack `a b ⟨g, rfl⟩`. Conclude with `⟨g, (hπ g b).symm⟩`. Set `q : MulAction.orbitRel.Quotient G X → MulAction.orbitRel.Quotient G Y` to `Quotient.map π (fun a b h => MulAction.orbitRel_apply.2 (hmem a b (MulAction.orbitRel_apply.1 h)))`.

Establish `hq : ∀ x : X, q (Quotient.mk _ x) = Quotient.mk _ (π x)` using `fun x => rfl`. Establish `hrep : ∀ (oX : MulAction.orbitRel.Quotient G X) (y : Y), q oX = Quotient.mk _ y → ∃ x0, π x0 = y ∧ Quotient.mk _ x0 = oX`. Introduce `oX y h`. Establish `h1 : q oX = Quotient.mk _ (π (Quotient.out oX))`. Rewrite using `[← hq, Quotient.out_eq]`.

Rewrite `h` using `[h1]`. Establish `h2 : y ∈ MulAction.orbit G (π (Quotient.out oX))` using `MulAction.orbitRel_apply.1 (Quotient.exact h.symm)`. Take `⟨g, hg⟩` from `h2`. Use `⟨g • Quotient.out oX, by rw [hπ]; exact hg, ?_⟩` and prove the remaining obligations. Rewrite using `[← Quotient.out_eq oX]`.

Conclude with `Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, by rw [Quotient.out_eq]⟩)`. Set `F : X → ℚ` to `fun x => w (π x) * ((MulAction.stabilizer G x).relIndex Gc : ℚ)`. Set `H : Y → ℚ` to `fun y => w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)`. Establish `hF : ∀ x x' : X, x' ∈ MulAction.orbit G x → F x' = F x`. Introduce and unpack `x x' ⟨g, rfl⟩`.

Simplify using `only [F, hπ, hw, stabilizer_smul_eq]`. Use `haveI : ∀ oY : MulAction.orbitRel.Quotient G Y, Finite ↥(π ⁻¹' {Quotient.out oY}) := fun oY => (hfin _).to_subtype`. Use `haveI hXf : Finite (MulAction.orbitRel.Quotient G X) := by`. Use `Finite.of_surjective (fun p : (Σ oY : MulAction.orbitRel.Quotient G Y, ↥(π ⁻¹' {Quotient.out oY})) => (Quotient.mk _ (p.2 : X) : MulAction.orbitRel.Quotient G X)) ?_` and prove the remaining obligations. Introduce `oX`.

Take `⟨x0, hx0, hx0'⟩` from `hrep oX (Quotient.out (q oX)) (Quotient.out_eq _).symm`. Conclude with `⟨⟨q oX, ⟨x0, hx0⟩⟩, hx0'⟩`. Use `haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)`. Use `haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)`. Establish `hL : ∀ oX : MulAction.orbitRel.Quotient G X, w (π (Quotient.out oX)) * ((MulAction.stabilizer G (Quotient.out oX)).relIndex Gc : ℚ) = F (Quotient.out oX)` using `fun _ => rfl`.

Establish `hR : ∀ oY : MulAction.orbitRel.Quotient G Y, w (Quotient.out oY) * ((π ⁻¹' {(Quotient.out oY)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out oY)).relIndex Gc : ℚ) = H (Quotient.out oY)` using `fun _ => rfl`. Simplify using `only [hL, hR]`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ q]`. Use `Finset.sum_congr rfl (fun oY _ => ?_)` and prove the remaining obligations. Use `set y := Quotient.out oY with hy`.

Establish `hyo : Quotient.mk _ y = oY` using `Quotient.out_eq oY`. Use `set S := (hfin y).toFinset with hS`. Establish `hcard : (π ⁻¹' {y}).ncard = S.card` using `Set.ncard_eq_toFinset_card _ (hfin y)`. Establish `hmaps : (S : Set X).MapsTo (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X)) (Finset.univ.filter (fun oX => q oX = oY) : Finset _)`. Introduce `x hx`.

Simplify using `only [hS, Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx`. Simplify using `[hq, hx, hyo]`. Establish `hsum` using `Finset.card_eq_sum_card_fiberwise hmaps`. Use `show _ = w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)`. Rewrite using `[hcard, hsum]`.

Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun oX hoX => ?_)` and prove the remaining obligations. Establish `hqo : q oX = Quotient.mk _ y`. Rewrite using `[hyo]`.

Simplify using `using hoX`. Take `⟨x0, hx0, hx0'⟩` from `hrep oX y hqo`. Establish `hout : Quotient.out oX ∈ MulAction.orbit G x0`. Apply `MulAction.orbitRel_apply.1` to reduce the goal to its premises. Apply `Quotient.exact` to reduce the goal to its premises.

Rewrite using `[Quotient.out_eq, hx0']`. Rewrite using `[hF x0 _ hout]`. Establish `hfilt : ((S.filter (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = oX) : Finset X) : Set X) = {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0}`. Use extensionality with `x`. Simplify using `only [hS, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hx0]`.

Rewrite using `[← hx0']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, MulAction.orbitRel_apply.1 (Quotient.exact h2)⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, Quotient.sound (MulAction.orbitRel_apply.2 h2)⟩`. Rewrite using `[← Set.ncard_coe_finset, hfilt, ncard_fibre_inter_orbit π hπ x0]`. Establish `hle1 : MulAction.stabilizer G x0 ≤ MulAction.stabilizer G (π x0)`. Introduce `g hg`. Rewrite `hg`, the goal using `[MulAction.mem_stabilizer_iff]`.

Rewrite using `[← hπ, hg]`. Rewrite `hle1` using `[hx0]`. Establish `hle2 : MulAction.stabilizer G y ≤ Gc` using `(hstab y).1`. Establish `hmul` using `Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2`. Simplify using `only [F, hx0]`.

Rewrite using `[← hmul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem counting_principle : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  intro G X Y _ _ _ Gc π hπ hfin hstab hY w hw
  classical
  have hmem : ∀ a b : X, a ∈ MulAction.orbit G b → π a ∈ MulAction.orbit G (π b) := by
    rintro a b ⟨g, rfl⟩; exact ⟨g, (hπ g b).symm⟩
  let q : MulAction.orbitRel.Quotient G X → MulAction.orbitRel.Quotient G Y :=
    Quotient.map π (fun a b h => MulAction.orbitRel_apply.2 (hmem a b (MulAction.orbitRel_apply.1 h)))
  have hq : ∀ x : X, q (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl

  have hrep : ∀ (oX : MulAction.orbitRel.Quotient G X) (y : Y), q oX = Quotient.mk _ y →
      ∃ x0, π x0 = y ∧ Quotient.mk _ x0 = oX := by
    intro oX y h
    have h1 : q oX = Quotient.mk _ (π (Quotient.out oX)) := by
      rw [← hq, Quotient.out_eq]
    rw [h1] at h
    have h2 : y ∈ MulAction.orbit G (π (Quotient.out oX)) :=
      MulAction.orbitRel_apply.1 (Quotient.exact h.symm)
    obtain ⟨g, hg⟩ := h2
    refine ⟨g • Quotient.out oX, by rw [hπ]; exact hg, ?_⟩
    rw [← Quotient.out_eq oX]
    exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, by rw [Quotient.out_eq]⟩)

  let F : X → ℚ := fun x => w (π x) * ((MulAction.stabilizer G x).relIndex Gc : ℚ)
  let H : Y → ℚ := fun y => w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  have hF : ∀ x x' : X, x' ∈ MulAction.orbit G x → F x' = F x := by
    rintro x x' ⟨g, rfl⟩
    simp only [F, hπ, hw, stabilizer_smul_eq]

  haveI : ∀ oY : MulAction.orbitRel.Quotient G Y, Finite ↥(π ⁻¹' {Quotient.out oY}) :=
    fun oY => (hfin _).to_subtype
  haveI hXf : Finite (MulAction.orbitRel.Quotient G X) := by
    refine Finite.of_surjective
      (fun p : (Σ oY : MulAction.orbitRel.Quotient G Y, ↥(π ⁻¹' {Quotient.out oY})) =>
        (Quotient.mk _ (p.2 : X) : MulAction.orbitRel.Quotient G X)) ?_
    intro oX
    obtain ⟨x0, hx0, hx0'⟩ := hrep oX (Quotient.out (q oX)) (Quotient.out_eq _).symm
    exact ⟨⟨q oX, ⟨x0, hx0⟩⟩, hx0'⟩
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)
  have hL : ∀ oX : MulAction.orbitRel.Quotient G X,
      w (π (Quotient.out oX)) * ((MulAction.stabilizer G (Quotient.out oX)).relIndex Gc : ℚ) = F (Quotient.out oX) := fun _ => rfl
  have hR : ∀ oY : MulAction.orbitRel.Quotient G Y,
      w (Quotient.out oY) * ((π ⁻¹' {(Quotient.out oY)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out oY)).relIndex Gc : ℚ) = H (Quotient.out oY) := fun _ => rfl
  simp only [hL, hR]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ q]
  refine Finset.sum_congr rfl (fun oY _ => ?_)
  set y := Quotient.out oY with hy
  have hyo : Quotient.mk _ y = oY := Quotient.out_eq oY
  set S := (hfin y).toFinset with hS
  have hcard : (π ⁻¹' {y}).ncard = S.card := Set.ncard_eq_toFinset_card _ (hfin y)
  have hmaps : (S : Set X).MapsTo (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X))
      (Finset.univ.filter (fun oX => q oX = oY) : Finset _) := by
    intro x hx
    simp only [hS, Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [hq, hx, hyo]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  show _ = w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  rw [hcard, hsum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun oX hoX => ?_)
  have hqo : q oX = Quotient.mk _ y := by
    rw [hyo]; simpa using hoX
  obtain ⟨x0, hx0, hx0'⟩ := hrep oX y hqo
  have hout : Quotient.out oX ∈ MulAction.orbit G x0 := by
    apply MulAction.orbitRel_apply.1
    apply Quotient.exact
    rw [Quotient.out_eq, hx0']
  rw [hF x0 _ hout]
  have hfilt : ((S.filter (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = oX) : Finset X) : Set X)
      = {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} := by
    ext x
    simp only [hS, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq, hx0]
    rw [← hx0']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, MulAction.orbitRel_apply.1 (Quotient.exact h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Quotient.sound (MulAction.orbitRel_apply.2 h2)⟩
  rw [← Set.ncard_coe_finset, hfilt, ncard_fibre_inter_orbit π hπ x0]
  have hle1 : MulAction.stabilizer G x0 ≤ MulAction.stabilizer G (π x0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hπ, hg]
  rw [hx0] at hle1
  have hle2 : MulAction.stabilizer G y ≤ Gc := (hstab y).1
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  simp only [F, hx0]
  rw [← hmul]
  push_cast
  ring

end GlobalTheory.OrbitCounting
