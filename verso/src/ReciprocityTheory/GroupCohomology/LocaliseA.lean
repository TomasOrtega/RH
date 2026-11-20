import ReciprocityTheory.GroupCohomology.TransgressionStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.Coh

open Cx Function

universe u

section Alg

variable {R : Type u} [CommRing R] {A B : Cx R}

/- English proof (translation)
The claim follows from `map_smul _ _ _`.
-/
theorem cx_smul_d {n : ℕ} (t : R) (x : B.X n) : B.d n (t • x) = t • B.d n x := map_smul _ _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Proceed by induction on `c using H_ind with`. Consider the case `h x hx`.

Rewrite `hc` using `[Module.algebraMap_end_apply, cls_smul, cls_eq_zero_iff]`. Rewrite using `[cls_eq_zero_iff]`. Consider the cases of `n with`. Consider the case `zero`. Establish `h0 : t • x = 0` using `hc`.

Conclude with `(ht 0).1 (h0.trans (smul_zero t).symm)`. Consider the case `succ n`. Take `⟨y, hy⟩` from `hc`. Take `⟨y', rfl⟩` from `(ht n).2 y`. Use `⟨y', (ht (n + 1)).1 ?_⟩` and prove the remaining obligations.

Use `show t • B.d n y' = t • x`. Rewrite using `[← cx_smul_d, hy]`. Introduce `c`. Proceed by induction on `c using H_ind with`. Consider the case `h x hx`.

Take `⟨x', rfl⟩` from `(ht n).2 x`. Establish `hx' : B.d n x' = 0` using `(ht (n + 1)).1 (by show t • B.d n x' = t • 0`. Rewrite using `[← cx_smul_d, smul_zero]`. Conclude with `hx)`. Conclude with `⟨B.cls n x' hx', by rw [Module.algebraMap_end_apply, cls_smul]⟩`.
-/
theorem bij_H_of_bij (t : R) (ht : ∀ n, Bijective fun x : B.X n => t • x) (n : ℕ) :
    Bijective (algebraMap R (Module.End R (B.H n)) t) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Module.algebraMap_end_apply, cls_smul, cls_eq_zero_iff] at hc
      rw [cls_eq_zero_iff]
      cases n with
      | zero =>
        have h0 : t • x = 0 := hc
        exact (ht 0).1 (h0.trans (smul_zero t).symm)
      | succ n =>
        obtain ⟨y, hy⟩ := hc
        obtain ⟨y', rfl⟩ := (ht n).2 y
        refine ⟨y', (ht (n + 1)).1 ?_⟩
        show t • B.d n y' = t • x
        rw [← cx_smul_d, hy]
  · intro c
    induction c using H_ind with
    | h x hx =>
      obtain ⟨x', rfl⟩ := (ht n).2 x
      have hx' : B.d n x' = 0 := (ht (n + 1)).1 (by
        show t • B.d n x' = t • 0
        rw [← cx_smul_d, smul_zero]; exact hx)
      exact ⟨B.cls n x' hx', by rw [Module.algebraMap_end_apply, cls_smul]⟩

/- English proof (translation)
Introduce and unpack `⟨_, k, rfl⟩`. Use `show IsUnit (algebraMap R (Module.End R (B.H n)) (t ^ k))`. Rewrite using `[map_pow]`. Conclude with `((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht n)).pow k`. Use `surj := by`.

Introduce `y`. Proceed by induction on `y using H_ind with`. Consider the case `h x hx`. Take `⟨m, a, ha⟩` from `hc n x`. Establish `ha0 : A.d n a = 0` using `(hj (n + 1)) (by`.

Rewrite using `[j.comm, ha, cx_smul_d, hx, smul_zero, map_zero])`. Use `⟨(A.cls n a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩` and prove the remaining obligations. Use `show (t ^ m) • B.cls n x hx = j.H n (A.cls n a ha0)`. Rewrite using `[cls_smul, Hom.H_cls]`. Conclude with `cls_congr _ _ ha.symm`.

Use `exists_of_eq := by`. Establish `key : ∀ z : A.H n, j.H n z = 0 → ∃ c : Submonoid.powers t, c • z = 0`. Introduce `z hz`. Proceed by induction on `z using H_ind with`. Consider the case `h g hg`.

Rewrite `hz` using `[Hom.H_cls, cls_eq_zero_iff]`. Consider the cases of `n with`. Consider the case `zero`. Establish `h0 : j.f 0 g = 0` using `hz`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Rewrite using `[one_smul, cls_eq_zero_iff]`. Conclude with `(hj 0) (h0.trans (map_zero _).symm)`. Consider the case `succ n`. Take `⟨h, hh⟩` from `hz`. Take `⟨m, k, hk⟩` from `hc n h`.

Use `⟨⟨t ^ m, m, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show (t ^ m) • A.cls (n + 1) g hg = 0`. Rewrite using `[cls_smul, cls_eq_zero_iff]`. Use `⟨k, (hj (n + 1)) ?_⟩` and prove the remaining obligations. Rewrite using `[j.comm, hk, cx_smul_d, hh, map_smul]`.

Introduce `x₁ x₂ h`. Take `⟨c, hc'⟩` from `key (x₁ - x₂) (by rw [map_sub, h, sub_self])`. Conclude with `⟨c, by rw [smul_sub, sub_eq_zero] at hc'; exact hc'⟩`.
-/
theorem isLocalized_of_cx (j : Hom A B) (t : R) (hj : ∀ n, Injective (j.f n))
    (ht : ∀ n, Bijective fun x : B.X n => t • x)
    (hc : ∀ n (x : B.X n), ∃ (m : ℕ) (y : A.X n), j.f n y = t ^ m • x) (n : ℕ) :
    IsLocalizedModule (Submonoid.powers t) (j.H n) where
  map_units := by
    rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap R (Module.End R (B.H n)) (t ^ k))
    rw [map_pow]
    exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht n)).pow k
  surj := by
    intro y
    induction y using H_ind with
    | h x hx =>
      obtain ⟨m, a, ha⟩ := hc n x
      have ha0 : A.d n a = 0 := (hj (n + 1)) (by
        rw [j.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
      refine ⟨(A.cls n a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
      show (t ^ m) • B.cls n x hx = j.H n (A.cls n a ha0)
      rw [cls_smul, Hom.H_cls]
      exact cls_congr _ _ ha.symm
  exists_of_eq := by
    have key : ∀ z : A.H n, j.H n z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
      intro z hz
      induction z using H_ind with
      | h g hg =>
        rw [Hom.H_cls, cls_eq_zero_iff] at hz
        cases n with
        | zero =>
          have h0 : j.f 0 g = 0 := hz
          refine ⟨1, ?_⟩
          rw [one_smul, cls_eq_zero_iff]
          exact (hj 0) (h0.trans (map_zero _).symm)
        | succ n =>
          obtain ⟨h, hh⟩ := hz
          obtain ⟨m, k, hk⟩ := hc n h
          refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
          show (t ^ m) • A.cls (n + 1) g hg = 0
          rw [cls_smul, cls_eq_zero_iff]
          refine ⟨k, (hj (n + 1)) ?_⟩
          rw [j.comm, hk, cx_smul_d, hh, map_smul]
    intro x₁ x₂ h
    obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
    exact ⟨c, by rw [smul_sub, sub_eq_zero] at hc'; exact hc'⟩

end Alg

section Trunc

variable {R : Type u} [CommRing R] (A : Cx R) (L : Submodule R (A.H 1))

def truncW : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊤
  | 1 => (L.comap ((A.B 1).comap (A.Z 1).subtype).mkQ).map (A.Z 1).subtype
  | _ + 2 => ⊥

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z.2, hz⟩`. Introduce and unpack `⟨hx, h⟩`. Conclude with `⟨⟨x, hx⟩, h, rfl⟩`.
-/
theorem mem_truncW_one {x : A.X 1} :
    x ∈ truncW A L 1 ↔ ∃ hx : A.d 1 x = 0, A.cls 1 x hx ∈ L := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

/- English proof (translation)
Use `match n, x, hx with`. Consider the case `0, x, _`. Rewrite using `[mem_truncW_one]`. Use `⟨A.dd 0 x, ?_⟩` and prove the remaining obligations. Rewrite using `[cls_d]`.

Conclude with `L.zero_mem`. Consider the case `1, x, hx`. Take `⟨hx0, _⟩` from `(mem_truncW_one A L).1 hx`. Use `show A.d 1 x ∈ (⊥ : Submodule R _)`. Rewrite using `[hx0]`.

Conclude with `Submodule.zero_mem _`. Consider the case `n + 2, x, hx`. Establish `: x = 0` using `(Submodule.mem_bot R).1 hx`. Substitute `this` using the available equality. Rewrite using `[map_zero]`.

Conclude with `Submodule.zero_mem _`.
-/
theorem truncW_d (n : ℕ) (x : A.X n) (hx : x ∈ truncW A L n) : A.d n x ∈ truncW A L (n + 1) := by
  match n, x, hx with
  | 0, x, _ =>
    rw [mem_truncW_one]
    refine ⟨A.dd 0 x, ?_⟩
    rw [cls_d]; exact L.zero_mem
  | 1, x, hx =>
    obtain ⟨hx0, _⟩ := (mem_truncW_one A L).1 hx
    show A.d 1 x ∈ (⊥ : Submodule R _)
    rw [hx0]; exact Submodule.zero_mem _
  | n + 2, x, hx =>
    have : x = 0 := (Submodule.mem_bot R).1 hx
    subst this
    rw [map_zero]; exact Submodule.zero_mem _

def truncCx : Cx R where
  X n := truncW A L n
  d n := (A.d n).restrict fun x hx => truncW_d A L n x hx
  dd n x := Subtype.ext (A.dd n x.1)

def truncHom : Hom (truncCx A L) A where
  f n := (truncW A L n).subtype
  comm _ _ := rfl

end Trunc

end ReciprocityTheory.Coh
