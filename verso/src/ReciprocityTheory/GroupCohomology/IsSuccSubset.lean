import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.Coh

noncomputable section

universe u

open Cx

namespace InflationTower

variable {R : Type u} [CommRing R]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma H_mk {A B : Cx R} (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl

/- English proof (translation)
Rewrite `h` using `[H_mk, Submodule.Quotient.eq, Submodule.mem_comap]`. Consider the cases of `n with`. Consider the case `zero`. Use `⟨z, rfl, ?_⟩` and prove the remaining obligations. Establish `h' : ((φ.Z 0 z - w : B.Z 0) : B.X 0) = 0` using `h`.

Conclude with `sub_eq_zero.mp (Subtype.ext h')`. Consider the case `succ k`. Take `⟨c, hc⟩` from `h`. Take `⟨c', rfl⟩` from `hs k c`. Establish `hdc : A.d (k+1) (A.d k c') = 0` using `A.dd k c'`.

Use `⟨z - ⟨A.d k c', hdc⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap]`. Use `⟨-c', ?_⟩` and prove the remaining obligations. Use `show A.d k (-c') = (z : A.X (k+1)) - A.d k c' - z`. Rewrite using `[map_neg]`.

Normalize the expressions using the abelian group laws. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hc' : B.d k (φ.f k c') = φ.f (k+1) z - w` using `hc`. Use `show φ.f (k+1) ((z : A.X (k+1)) - A.d k c') = w`. Rewrite using `[map_sub, φ.comm, hc']`.

Normalize the expressions using the abelian group laws.
-/
lemma lift_cocycle {A B : Cx R} (φ : Hom A B) (hs : ∀ n, Function.Surjective (φ.f n)) (n : ℕ)
    (z : A.Z n) (w : B.Z n) (h : φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk w) :
    ∃ z' : A.Z n, (Submodule.Quotient.mk z' : A.H n) = Submodule.Quotient.mk z ∧ φ.Z n z' = w := by
  rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap] at h
  cases n with
  | zero =>
    refine ⟨z, rfl, ?_⟩
    have h' : ((φ.Z 0 z - w : B.Z 0) : B.X 0) = 0 := h
    exact sub_eq_zero.mp (Subtype.ext h')
  | succ k =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨c', rfl⟩ := hs k c
    have hdc : A.d (k+1) (A.d k c') = 0 := A.dd k c'
    refine ⟨z - ⟨A.d k c', hdc⟩, ?_, ?_⟩
    · rw [Submodule.Quotient.eq, Submodule.mem_comap]
      refine ⟨-c', ?_⟩
      show A.d k (-c') = (z : A.X (k+1)) - A.d k c' - z
      rw [map_neg]; abel
    · apply Subtype.ext
      have hc' : B.d k (φ.f k c') = φ.f (k+1) z - w := hc
      show φ.f (k+1) ((z : A.X (k+1)) - A.d k c') = w
      rw [map_sub, φ.comm, hc']; abel

/- English proof (translation)
Establish `step : ∀ m (z : (A m).Z n), (Submodule.Quotient.mk z : (A m).H n) = y m → ∃ z' : (A (m+1)).Z n, (Submodule.Quotient.mk z' : (A (m+1)).H n) = y (m+1) ∧ (τ m).Z n z' = z`. Introduce `m z hz`. Take `⟨w, hw⟩` from `Submodule.Quotient.mk_surjective _ (y (m+1))`. Take `⟨z', h1, h2⟩` from `lift_cocycle (τ m) (hT.surj m) n w z (by rw [hw, hy, hz])`. Conclude with `⟨z', h1.trans hw, h2⟩`.

Set `seq : ∀ m, {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m}` to `fun m => Nat.rec (motive := fun m => {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m}) ⟨Classical.choose (Submodule.Quotient.mk_surjective _ (y 0)), Classical.choose_spec (Submodule.Quotient.mk_surjective _ (y 0))⟩ (fun m s => ⟨Classical.choose (step m s.1 s.2), (Cl …`. Establish `hseq : ∀ m, (τ m).Z n (seq (m+1)).1 = (seq m).1` using `fun m => (Classical.choose_spec (step m (seq m).1 (seq m).2)).2`. Take `⟨x, hx⟩` from `hT.lift n (fun m => ((seq m).1 : (A m).X n)) (fun m => congrArg Subtype.val (hseq m))`. Establish `hdx : L.d n x = 0`. Apply `hT.ext` to reduce the goal to its premises.

Introduce `m`. Rewrite using `[(π m).comm, hx]`. Conclude with `(seq m).1.2`. Use `⟨Submodule.Quotient.mk ⟨x, hdx⟩, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[H_mk, ← (seq m).2]`.

Use `congr 1`. Conclude with `Subtype.ext (hx m)`.
-/
theorem surj_part (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (n : ℕ) (y : ∀ m, (A m).H n) (hy : ∀ m, (τ m).H n (y (m + 1)) = y m) :
    ∃ x, ∀ m, (π m).H n x = y m := by
  have step : ∀ m (z : (A m).Z n), (Submodule.Quotient.mk z : (A m).H n) = y m →
      ∃ z' : (A (m+1)).Z n, (Submodule.Quotient.mk z' : (A (m+1)).H n) = y (m+1) ∧ (τ m).Z n z' = z := by
    intro m z hz
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (y (m+1))
    obtain ⟨z', h1, h2⟩ := lift_cocycle (τ m) (hT.surj m) n w z (by rw [hw, hy, hz])
    exact ⟨z', h1.trans hw, h2⟩
  let seq : ∀ m, {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m} := fun m =>
    Nat.rec (motive := fun m => {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m})
      ⟨Classical.choose (Submodule.Quotient.mk_surjective _ (y 0)),
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (y 0))⟩
      (fun m s => ⟨Classical.choose (step m s.1 s.2), (Classical.choose_spec (step m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).Z n (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (step m (seq m).1 (seq m).2)).2
  obtain ⟨x, hx⟩ := hT.lift n (fun m => ((seq m).1 : (A m).X n)) (fun m => congrArg Subtype.val (hseq m))
  have hdx : L.d n x = 0 := by
    apply hT.ext
    intro m
    rw [(π m).comm, hx]; exact (seq m).1.2
  refine ⟨Submodule.Quotient.mk ⟨x, hdx⟩, fun m => ?_⟩
  rw [H_mk, ← (seq m).2]
  congr 1; exact Subtype.ext (hx m)

def Hs (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) : ℕ → ∀ m, Submodule R ((A m).H k)
  | 0 => fun _ => ⊤
  | j + 1 => fun m => (Hs A τ k j (m + 1)).map ((τ m).H k)

def Is (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1)) :
    ℕ → ∀ m, Set ((A m).X k)
  | 0 => fun m => {b | (A m).d k b = c m}
  | j + 1 => fun m => (τ m).f k '' Is A τ k c j (m + 1)

section Inj

variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `m p hp q`. Establish `hp' : (A m).d k p = c m` using `hp`.

Use `show (A m).d k q = c m ↔ _`. Simplify using `only [Hs, Submodule.mem_top, exists_prop, and_true, map_sub, hp', sub_eq_zero]`. Consider the case `succ j ih`. Introduce `m p hp q`. Take `⟨p', hp', rfl⟩` from `hp`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q', hq', rfl⟩`. Take `⟨hx, hmem⟩` from `(ih (m+1) p' hp' q').1 hq'`. Establish `hx' : (A m).d k ((τ m).f k q' - (τ m).f k p') = 0`. Rewrite using `[← map_sub, ← (τ m).comm, hx, map_zero]`.

Use `⟨hx', ?_⟩` and prove the remaining obligations. Establish `he : (Submodule.Quotient.mk ⟨(τ m).f k q' - (τ m).f k p', hx'⟩ : (A m).H k) = (τ m).H k (Submodule.Quotient.mk ⟨q' - p', hx⟩)`. Rewrite using `[H_mk]`. Use `congr 1`. Conclude with `Subtype.ext (map_sub _ _ _).symm`.

Rewrite using `[he]`. Conclude with `Submodule.mem_map_of_mem hmem`. Introduce and unpack `⟨hx, hmem⟩`. Take `⟨h, hh, he⟩` from `hmem`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ h`.

Take `⟨y', h1, h2⟩` from `lift_cocycle (τ m) (hs m) k y ⟨_, hx⟩ he`. Establish `h2' : (τ m).f k y' = q - (τ m).f k p'` using `congrArg Subtype.val h2`. Use `⟨p' + y', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ih (m+1) p' hp']`. Establish `hy0 : (A (m+1)).d k (p' + y' - p') = 0` using `by rw [add_sub_cancel_left]; exact y'.2`.

Use `⟨hy0, ?_⟩` and prove the remaining obligations. Establish `: (⟨p' + y' - p', hy0⟩ : (A (m+1)).Z k) = y'` using `Subtype.ext (add_sub_cancel_left _ _)`. Rewrite using `[this, h1]`. Conclude with `hh`. Rewrite using `[map_add, h2']`.

Normalize the expressions using the abelian group laws.
-/
lemma Is_torsor (hs : ∀ m n, Function.Surjective ((τ m).f n)) :
    ∀ j m p, p ∈ Is A τ k c j m → ∀ q, q ∈ Is A τ k c j m ↔
      ∃ hx : (A m).d k (q - p) = 0, (Submodule.Quotient.mk ⟨q - p, hx⟩ : (A m).H k) ∈ Hs A τ k j m := by
  intro j
  induction j with
  | zero =>
    intro m p hp q
    have hp' : (A m).d k p = c m := hp
    show (A m).d k q = c m ↔ _
    simp only [Hs, Submodule.mem_top, exists_prop, and_true, map_sub, hp', sub_eq_zero]
  | succ j ih =>
    intro m p hp q
    obtain ⟨p', hp', rfl⟩ := hp
    constructor
    · rintro ⟨q', hq', rfl⟩
      obtain ⟨hx, hmem⟩ := (ih (m+1) p' hp' q').1 hq'
      have hx' : (A m).d k ((τ m).f k q' - (τ m).f k p') = 0 := by
        rw [← map_sub, ← (τ m).comm, hx, map_zero]
      refine ⟨hx', ?_⟩
      have he : (Submodule.Quotient.mk ⟨(τ m).f k q' - (τ m).f k p', hx'⟩ : (A m).H k) =
          (τ m).H k (Submodule.Quotient.mk ⟨q' - p', hx⟩) := by
        rw [H_mk]; congr 1; exact Subtype.ext (map_sub _ _ _).symm
      rw [he]
      exact Submodule.mem_map_of_mem hmem
    · rintro ⟨hx, hmem⟩
      obtain ⟨h, hh, he⟩ := hmem
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      obtain ⟨y', h1, h2⟩ := lift_cocycle (τ m) (hs m) k y ⟨_, hx⟩ he
      have h2' : (τ m).f k y' = q - (τ m).f k p' := congrArg Subtype.val h2
      refine ⟨p' + y', ?_, ?_⟩
      · rw [ih (m+1) p' hp']
        have hy0 : (A (m+1)).d k (p' + y' - p') = 0 := by rw [add_sub_cancel_left]; exact y'.2
        refine ⟨hy0, ?_⟩
        have : (⟨p' + y' - p', hy0⟩ : (A (m+1)).Z k) = y' := Subtype.ext (add_sub_cancel_left _ _)
        rw [this, h1]; exact hh
      · rw [map_add, h2']; abel

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact hP`. Consider the case `succ j ih => intro m`. Conclude with `(ih (m+1)).image _`.
-/
lemma Is_nonempty (hP : ∀ m, ∃ b, (A m).d k b = c m) : ∀ j m, (Is A τ k c j m).Nonempty := by
  intro j
  induction j with
  | zero => exact hP
  | succ j ih => intro m; exact (ih (m+1)).image _

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce and unpack `m _ ⟨b, hb, rfl⟩`. Establish `hb' : (A (m+1)).d k b = c (m+1)` using `hb`.

Use `show (A m).d k ((τ m).f k b) = c m`. Rewrite using `[← (τ m).comm, hb', hc]`. Consider the case `succ j ih => intro m`. Conclude with `Set.image_mono (ih (m+1))`.
-/
lemma Is_succ_subset (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) :
    ∀ j m, Is A τ k c (j+1) m ⊆ Is A τ k c j m := by
  intro j
  induction j with
  | zero =>
    rintro m _ ⟨b, hb, rfl⟩
    have hb' : (A (m+1)).d k b = c (m+1) := hb
    show (A m).d k ((τ m).f k b) = c m
    rw [← (τ m).comm, hb', hc]
  | succ j ih => intro m; exact Set.image_mono (ih (m+1))

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro m`. Conclude with `le_top`. Consider the case `succ j ih => intro m`.

Conclude with `Submodule.map_mono (ih (m+1))`.
-/
lemma Hs_succ_le : ∀ j m, Hs A τ k (j+1) m ≤ Hs A τ k j m := by
  intro j
  induction j with
  | zero => intro m; exact le_top
  | succ j ih => intro m; exact Submodule.map_mono (ih (m+1))

end Inj

section Inj2

variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))

/- English proof (translation)
The claim follows from `antitone_nat_of_succ_le fun j => Is_succ_subset A τ k c hc j m`.
-/
lemma Is_anti (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) (m : ℕ) :
    Antitone fun j => Is A τ k c j m :=
  antitone_nat_of_succ_le fun j => Is_succ_subset A τ k c hc j m

/- English proof (translation)
The claim follows from `antitone_nat_of_succ_le fun j => Hs_succ_le A τ k j m`.
-/
lemma Hs_anti (m : ℕ) : Antitone fun j => Hs A τ k j m :=
  antitone_nat_of_succ_le fun j => Hs_succ_le A τ k j m

/- English proof (translation)
Take `⟨J, hJ⟩` from `IsArtinian.monotone_stabilizes (⟨fun j => OrderDual.toDual (Hs A τ k j m), fun _ _ h => Hs_anti A τ k m h⟩ : ℕ →o (Submodule R ((A m).H k))ᵒᵈ)`. Conclude with `⟨J, fun j hj => (congrArg OrderDual.ofDual (hJ j hj)).symm⟩`.
-/
lemma Hs_stab (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Hs A τ k j m = Hs A τ k J m := by
  obtain ⟨J, hJ⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (Hs A τ k j m), fun _ _ h => Hs_anti A τ k m h⟩ :
      ℕ →o (Submodule R ((A m).H k))ᵒᵈ)
  exact ⟨J, fun j hj => (congrArg OrderDual.ofDual (hJ j hj)).symm⟩

/- English proof (translation)
Take `⟨J, hJ⟩` from `Hs_stab A τ k hA m`. Use `⟨J, fun j hj => ?_⟩` and prove the remaining obligations. Apply `le_antisymm (Is_anti A τ k c hc m hj)` to reduce the goal to its premises. Take `⟨p, hp⟩` from `Is_nonempty A τ k c hP j m`. Establish `hpJ` using `Is_anti A τ k c hc m hj hp`.

Introduce `q hq`. Rewrite using `[Is_torsor A τ k c hs j m p hp, hJ j hj]`. Conclude with `(Is_torsor A τ k c hs J m p hpJ q).1 hq`.
-/
lemma Is_stab (hs : ∀ m n, Function.Surjective ((τ m).f n)) (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m)
    (hP : ∀ m, ∃ b, (A m).d k b = c m) (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m := by
  obtain ⟨J, hJ⟩ := Hs_stab A τ k hA m
  refine ⟨J, fun j hj => ?_⟩
  apply le_antisymm (Is_anti A τ k c hc m hj)
  obtain ⟨p, hp⟩ := Is_nonempty A τ k c hP j m
  have hpJ := Is_anti A τ k c hc m hj hp
  intro q hq
  rw [Is_torsor A τ k c hs j m p hp, hJ j hj]
  exact (Is_torsor A τ k c hs J m p hpJ q).1 hq

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hP : ∀ m, ∃ b, (A m).d k b = (π m).f (k+1) z`. Introduce `m`. Establish `h` using `hx m`. Rewrite `h` using `[H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Take `⟨b, hb⟩` from `h`. Conclude with `⟨b, hb⟩`. Set `c : ∀ m, (A m).X (k + 1)` to `fun m => (π m).f (k+1) z`. Establish `hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m` using `fun m => hT.compat m (k+1) z`. Establish `hstab : ∀ m, ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m` using `Is_stab A τ k c hT.surj hc hP hA`.

Set `J : ℕ → ℕ` to `fun m => Classical.choose (hstab m)`. Establish `hJ : ∀ m j, J m ≤ j → Is A τ k c j m = Is A τ k c (J m) m` using `fun m => Classical.choose_spec (hstab m)`. Set `S : ∀ m, Set ((A m).X k)` to `fun m => Is A τ k c (J m) m`. Establish `hS : ∀ m j, S m ⊆ Is A τ k c j m`. Introduce `m j`.

Break down `le_total j (J m) with h | h` into its components or cases. Conclude with `Is_anti A τ k c hc m h`. Rewrite using `[hJ m j h]`. Establish `hSsurj : ∀ m, ∀ s ∈ S m, ∃ t ∈ S (m+1), (τ m).f k t = s` using `fun m s hs => hS m (J (m+1) + 1) hs`. Establish `hS0 : (S 0).Nonempty` using `Is_nonempty A τ k c hP _ _`.

Set `seq : ∀ m, {b : (A m).X k // b ∈ S m}` to `fun m => Nat.rec (motive := fun m => {b : (A m).X k // b ∈ S m}) ⟨hS0.some, hS0.some_mem⟩ (fun m s => ⟨Classical.choose (hSsurj m s.1 s.2), (Classical.choose_spec (hSsurj m s.1 s.2)).1⟩) m`. Establish `hseq : ∀ m, (τ m).f k (seq (m+1)).1 = (seq m).1` using `fun m => (Classical.choose_spec (hSsurj m (seq m).1 (seq m).2)).2`. Take `⟨b, hb⟩` from `hT.lift k (fun m => (seq m).1) hseq`. Establish `hdb : L.d k b = z`. Rewrite using `[← sub_eq_zero]`.

Apply `hT.ext` to reduce the goal to its premises. Introduce `m`. Establish `h0 : (A m).d k (seq m).1 = c m` using `hS m 0 (seq m).2`. Rewrite using `[map_sub, (π m).comm, hb, h0, sub_self]`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`.

Conclude with `⟨b, hdb⟩`.
-/
theorem inj_part (L : Cx R) (π : ∀ m, Hom L (A m)) (hT : IsTowerLim A τ L π)
    (hA : ∀ m, IsArtinian R ((A m).H k)) (x : L.H (k + 1)) (hx : ∀ m, (π m).H (k + 1) x = 0) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ∀ m, ∃ b, (A m).d k b = (π m).f (k+1) z := by
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, hb⟩
  let c : ∀ m, (A m).X (k + 1) := fun m => (π m).f (k+1) z
  have hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m := fun m => hT.compat m (k+1) z
  have hstab : ∀ m, ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m :=
    Is_stab A τ k c hT.surj hc hP hA
  let J : ℕ → ℕ := fun m => Classical.choose (hstab m)
  have hJ : ∀ m j, J m ≤ j → Is A τ k c j m = Is A τ k c (J m) m := fun m => Classical.choose_spec (hstab m)
  let S : ∀ m, Set ((A m).X k) := fun m => Is A τ k c (J m) m
  have hS : ∀ m j, S m ⊆ Is A τ k c j m := by
    intro m j
    rcases le_total j (J m) with h | h
    · exact Is_anti A τ k c hc m h
    · rw [hJ m j h]
  have hSsurj : ∀ m, ∀ s ∈ S m, ∃ t ∈ S (m+1), (τ m).f k t = s := fun m s hs =>
    hS m (J (m+1) + 1) hs
  have hS0 : (S 0).Nonempty := Is_nonempty A τ k c hP _ _
  let seq : ∀ m, {b : (A m).X k // b ∈ S m} := fun m =>
    Nat.rec (motive := fun m => {b : (A m).X k // b ∈ S m}) ⟨hS0.some, hS0.some_mem⟩
      (fun m s => ⟨Classical.choose (hSsurj m s.1 s.2), (Classical.choose_spec (hSsurj m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).f k (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (hSsurj m (seq m).1 (seq m).2)).2
  obtain ⟨b, hb⟩ := hT.lift k (fun m => (seq m).1) hseq
  have hdb : L.d k b = z := by
    rw [← sub_eq_zero]
    apply hT.ext
    intro m
    have h0 : (A m).d k (seq m).1 = c m := hS m 0 (seq m).2
    rw [map_sub, (π m).comm, hb, h0, sub_self]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact ⟨b, hdb⟩

end Inj2

/- English proof (translation)
Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hz : (z : L.X 0) = 0`. Apply `hT.ext` to reduce the goal to its premises. Introduce `m`. Establish `h` using `hx m`.

Rewrite `h` using `[H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Conclude with `h`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, hz]`. Conclude with `Submodule.zero_mem _`.
-/
theorem inj_zero (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (x : L.H 0) (hx : ∀ m, (π m).H 0 x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : L.X 0) = 0 := by
    apply hT.ext
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    exact h
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, hz]
  exact Submodule.zero_mem _

end InflationTower

end

universe u

open InflationTower in
/- English proof (translation)
Introduce `R _ A τ L π hT n`. Use `⟨surj_part A τ L π hT n, fun hA x hx => ?_⟩` and prove the remaining obligations. Consider the cases of `n with`. Consider the case `zero => exact inj_zero A τ L π hT x hx`. Consider the case `succ k => exact inj_part A τ k L π hT (hA k rfl) x hx`.
-/
theorem tower_holds : TowerStatement.{u} := by
  intro R _ A τ L π hT n
  refine ⟨surj_part A τ L π hT n, fun hA x hx => ?_⟩
  cases n with
  | zero => exact inj_zero A τ L π hT x hx
  | succ k => exact inj_part A τ k L π hT (hA k rfl) x hx

end ReciprocityTheory.Coh
