import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.Coh

open Cx Function

universe u

namespace LongExactSequenceMaps

variable {R : Type u} [CommRing R] {A B C : Cx R}

/- English proof (translation)
Take `⟨⟨x, hx⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ h`. Conclude with `⟨x, hx, rfl⟩`.
-/
theorem cls_surj (A : Cx R) (n : ℕ) (h : A.H n) : ∃ x hx, h = A.cls n x hx := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  exact ⟨x, hx, rfl⟩

/- English proof (translation)
Unfold `Cx.cls`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `Iff.rfl`.
-/
theorem cls_eq_zero (A : Cx R) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) :
    A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem cls_congr (A : Cx R) (n : ℕ) (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0)
    (h : x = y) : A.cls n x hx = A.cls n y hy := by
  subst h
  rfl

/- English proof (translation)
Unfold `Cx.cls`. Rewrite using `[Submodule.Quotient.eq]`. Conclude with `Iff.rfl`.
-/
theorem cls_eq (A : Cx R) (n : ℕ) (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem H_cls (φ : Hom A B) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (by rw [← φ.comm, hx, map_zero]) := rfl

/- English proof (translation)
Use `show x ∈ LinearMap.range (A.d n) ↔ _`. Conclude with `LinearMap.mem_range`.
-/
theorem mem_B_succ (A : Cx R) (n : ℕ) (x : A.X (n + 1)) : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x := by
  show x ∈ LinearMap.range (A.d n) ↔ _
  exact LinearMap.mem_range

/- English proof (translation)
Use `show x ∈ (⊥ : Submodule R (A.X 0)) ↔ _`. Conclude with `Submodule.mem_bot R`.
-/
theorem mem_B_zero (A : Cx R) (x : A.X 0) : x ∈ A.B 0 ↔ x = 0 := by
  show x ∈ (⊥ : Submodule R (A.X 0)) ↔ _
  exact Submodule.mem_bot R

end LongExactSequenceMaps

namespace LongExactSequenceMaps

noncomputable section

variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)

/- English proof (translation)
Conclude with `(hs.exact n (i.f n a)).2 ⟨a, rfl⟩`.
-/
theorem p_i (hs : SES i p) (n : ℕ) (a : A.X n) : p.f n (i.f n a) = 0 := by
  exact (hs.exact n (i.f n a)).2 ⟨a, rfl⟩

def S (i : Hom A B) (n : ℕ) : Submodule R (B.X n) := (LinearMap.range (i.f (n + 1))).comap (B.d n)

def toRange (n : ℕ) : S i n →ₗ[R] LinearMap.range (i.f (n + 1)) :=
  ((B.d n).comp (S i n).subtype).codRestrict _ (fun b => b.2)

def pre (hs : SES i p) (n : ℕ) : S i n →ₗ[R] A.X (n + 1) :=
  (LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).symm.toLinearMap.comp (toRange i n)

/- English proof (translation)
Establish `key : ∀ y : LinearMap.range (i.f (n + 1)), i.f (n + 1) ((LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).symm y) = y` using `fun y => by`. Establish `h` using `congrArg Subtype.val ((LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).apply_symm_apply y)`. Simplify using `using h`. Simplify using `only [pre, LinearMap.comp_apply, LinearEquiv.coe_coe, key]`. Both sides reduce to the same expression.
-/
theorem i_pre (hs : SES i p) (n : ℕ) (b : S i n) : i.f (n + 1) (pre i p hs n b) = B.d n b := by
  have key : ∀ y : LinearMap.range (i.f (n + 1)),
      i.f (n + 1) ((LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).symm y) = y := fun y => by
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective (i.f (n + 1)) (hs.inj _)).apply_symm_apply y)
    simpa using h
  simp only [pre, LinearMap.comp_apply, LinearEquiv.coe_coe, key]
  rfl

/- English proof (translation)
Apply `hs.inj (n + 1 + 1)` to reduce the goal to its premises. Rewrite using `[map_zero, i.comm, i_pre, B.dd]`.
-/
theorem pre_d (hs : SES i p) (n : ℕ) (b : S i n) : A.d (n + 1) (pre i p hs n b) = 0 := by
  apply hs.inj (n + 1 + 1)
  rw [map_zero, i.comm, i_pre, B.dd]

/- English proof (translation)
Conclude with `hs.inj (n + 1) (by rw [i_pre, h])`.
-/
theorem pre_eq (hs : SES i p) (n : ℕ) (b : S i n) (a : A.X (n + 1)) (h : B.d n b = i.f (n + 1) a) :
    pre i p hs n b = a := by
  exact hs.inj (n + 1) (by rw [i_pre, h])

def θ (hs : SES i p) (n : ℕ) : S i n →ₗ[R] A.H (n + 1) :=
  (Submodule.mkQ _).comp ((pre i p hs n).codRestrict (A.Z (n + 1)) (fun b => pre_d i p hs n b))

/- English proof (translation)
Establish `hb : B.d n b ∈ LinearMap.range (i.f (n + 1))` using `b.2`. Take `⟨a, ha⟩` from `LinearMap.mem_range.1 hb`. Rewrite using `[← p.comm, ← ha, p_i i p hs]`.
-/
theorem pS_mem (hs : SES i p) (n : ℕ) (b : S i n) : C.d n (p.f n b) = 0 := by
  have hb : B.d n b ∈ LinearMap.range (i.f (n + 1)) := b.2
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 hb
  rw [← p.comm, ← ha, p_i i p hs]

def pS (hs : SES i p) (n : ℕ) : S i n →ₗ[R] C.H n :=
  (Submodule.mkQ _).comp (((p.f n).comp (S i n).subtype).codRestrict (C.Z n)
    (fun b => pS_mem i p hs n b))

/- English proof (translation)
Establish `e : pre i p hs n b = a` using `pre_eq i p hs n b a h`. Unfold `θ Cx.cls`. Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply]`. Use `congr 1`. Conclude with `Subtype.ext e`.
-/
theorem θ_apply (hs : SES i p) (n : ℕ) (b : S i n) (a : A.X (n + 1)) (ha : A.d (n + 1) a = 0)
    (h : B.d n b = i.f (n + 1) a) : θ i p hs n b = A.cls (n + 1) a ha := by
  have e : pre i p hs n b = a := pre_eq i p hs n b a h
  unfold θ Cx.cls
  rw [LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1
  exact Subtype.ext e

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pS_apply (hs : SES i p) (n : ℕ) (b : S i n) : pS i p hs n b = C.cls n (p.f n b) (pS_mem i p hs n b) := rfl

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `cls_surj C n h`. Take `⟨b, rfl⟩` from `hs.surj n c`. Establish `hdb : p.f (n + 1) (B.d n b) = 0` using `by rw [p.comm, hc]`. Take `⟨a, ha⟩` from `(hs.exact (n + 1) (B.d n b)).1 hdb`. Establish `had : A.d (n + 1) a = 0`.

Apply `hs.inj (n + 1 + 1)` to reduce the goal to its premises. Rewrite using `[map_zero, i.comm, ha, B.dd]`. Conclude with `⟨b, a, hc, had, ha.symm, rfl⟩`.
-/
theorem rep (hs : SES i p) (n : ℕ) (h : C.H n) : ∃ (b : B.X n) (a : A.X (n + 1)) (hc : C.d n (p.f n b) = 0)
    (_ : A.d (n + 1) a = 0), B.d n b = i.f (n + 1) a ∧ h = C.cls n (p.f n b) hc := by
  obtain ⟨c, hc, rfl⟩ := cls_surj C n h
  obtain ⟨b, rfl⟩ := hs.surj n c
  have hdb : p.f (n + 1) (B.d n b) = 0 := by rw [p.comm, hc]
  obtain ⟨a, ha⟩ := (hs.exact (n + 1) (B.d n b)).1 hdb
  have had : A.d (n + 1) a = 0 := by
    apply hs.inj (n + 1 + 1)
    rw [map_zero, i.comm, ha, B.dd]
  exact ⟨b, a, hc, had, ha.symm, rfl⟩

/- English proof (translation)
Introduce `h`. Take `⟨b, a, hc, ha, hba, rfl⟩` from `rep i p hs n h`. Conclude with `⟨⟨b, LinearMap.mem_range.2 ⟨a, hba.symm⟩⟩, rfl⟩`.
-/
theorem pS_surj (hs : SES i p) (n : ℕ) : Surjective (pS i p hs n) := by
  intro h
  obtain ⟨b, a, hc, ha, hba, rfl⟩ := rep i p hs n h
  exact ⟨⟨b, LinearMap.mem_range.2 ⟨a, hba.symm⟩⟩, rfl⟩

end

end LongExactSequenceMaps

namespace LongExactSequenceMaps

noncomputable section

variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)

/- English proof (translation)
Introduce `b hb`. Rewrite `hb`, the goal using `[LinearMap.mem_ker]`. Rewrite `hb` using `[pS_apply, cls_eq_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨a0, ha0⟩ : ∃ a0, B.d n b = i.f (n + 1) (A.d n a0) := by`. Consider the cases of `n with`.

Consider the case `zero`. Rewrite `hb` using `[mem_B_zero]`. Take `⟨a0, ha0⟩` from `(hs.exact 0 _).1 hb`. Conclude with `⟨a0, by rw [i.comm, ha0]⟩`. Consider the case `succ k`.

Rewrite `hb` using `[mem_B_succ]`. Take `⟨c', hc'⟩` from `hb`. Take `⟨b', rfl⟩` from `hs.surj k c'`. Establish `hp : p.f (k + 1) ((b : B.X (k + 1)) - B.d k b') = 0`. Rewrite using `[map_sub, p.comm, hc', sub_self]`.

Take `⟨a0, ha0⟩` from `(hs.exact (k + 1) _).1 hp`. Use `⟨a0, ?_⟩` and prove the remaining obligations. Rewrite using `[i.comm, ha0, map_sub, B.dd, sub_zero]`. Rewrite using `[θ_apply i p hs n b (A.d n a0) (A.dd n a0) ha0, cls_eq_zero, mem_B_succ]`. Conclude with `⟨a0, rfl⟩`.
-/
theorem ker_le (hs : SES i p) (n : ℕ) : LinearMap.ker (pS i p hs n) ≤ LinearMap.ker (θ i p hs n) := by
  intro b hb
  rw [LinearMap.mem_ker] at hb ⊢
  rw [pS_apply, cls_eq_zero] at hb
  obtain ⟨a0, ha0⟩ : ∃ a0, B.d n b = i.f (n + 1) (A.d n a0) := by
    cases n with
    | zero =>
      rw [mem_B_zero] at hb
      obtain ⟨a0, ha0⟩ := (hs.exact 0 _).1 hb
      exact ⟨a0, by rw [i.comm, ha0]⟩
    | succ k =>
      rw [mem_B_succ] at hb
      obtain ⟨c', hc'⟩ := hb
      obtain ⟨b', rfl⟩ := hs.surj k c'
      have hp : p.f (k + 1) ((b : B.X (k + 1)) - B.d k b') = 0 := by
        rw [map_sub, p.comm, hc', sub_self]
      obtain ⟨a0, ha0⟩ := (hs.exact (k + 1) _).1 hp
      refine ⟨a0, ?_⟩
      rw [i.comm, ha0, map_sub, B.dd, sub_zero]
  rw [θ_apply i p hs n b (A.d n a0) (A.dd n a0) ha0, cls_eq_zero, mem_B_succ]
  exact ⟨a0, rfl⟩

def conn (hs : SES i p) (n : ℕ) : C.H n →ₗ[R] A.H (n + 1) :=
  ((LinearMap.ker (pS i p hs n)).liftQ (θ i p hs n) (ker_le i p hs n)).comp
    (LinearMap.quotKerEquivOfSurjective (pS i p hs n) (pS_surj i p hs n)).symm.toLinearMap

/- English proof (translation)
Establish `e : (LinearMap.quotKerEquivOfSurjective (pS i p hs n) (pS_surj i p hs n)).symm (pS i p hs n b) = Submodule.Quotient.mk b`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `(LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm`. Simplify using `only [conn, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]`.
-/
theorem conn_pS (hs : SES i p) (n : ℕ) (b : S i n) : conn i p hs n (pS i p hs n b) = θ i p hs n b := by
  have e : (LinearMap.quotKerEquivOfSurjective (pS i p hs n) (pS_surj i p hs n)).symm
      (pS i p hs n b) = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]
    exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
  simp only [conn, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]

/- English proof (translation)
Introduce `n b a hc ha hba`. Establish `hbS : b ∈ S i n` using `LinearMap.mem_range.2 ⟨a, hba.symm⟩`. Conclude with `(conn_pS i p hs n ⟨b, hbS⟩).trans (θ_apply i p hs n ⟨b, hbS⟩ a ha hba)`.
-/
theorem conn_isConn (hs : SES i p) : IsConn i p (conn i p hs) := by
  intro n b a hc ha hba
  have hbS : b ∈ S i n := LinearMap.mem_range.2 ⟨a, hba.symm⟩
  exact (conn_pS i p hs n ⟨b, hbS⟩).trans (θ_apply i p hs n ⟨b, hbS⟩ a ha hba)

end

end LongExactSequenceMaps

namespace LongExactSequenceMaps

variable {R : Type u} [CommRing R] {A B C : Cx R} (i : Hom A B) (p : Hom B C)

/- English proof (translation)
Use function extensionality and compare the values at `n`. Use `LinearMap.ext fun h => ?_` and prove the remaining obligations. Take `⟨b, a, hc, ha, hba, rfl⟩` from `rep i p hs n h`. Rewrite using `[hδ n b a hc ha hba, hδ' n b a hc ha hba]`.
-/
theorem uniq (hs : SES i p) (δ δ' : ∀ n, C.H n →ₗ[R] A.H (n + 1)) (hδ : IsConn i p δ)
    (hδ' : IsConn i p δ') : δ = δ' := by
  funext n
  refine LinearMap.ext fun h => ?_
  obtain ⟨b, a, hc, ha, hba, rfl⟩ := rep i p hs n h
  rw [hδ n b a hc ha hba, hδ' n b a hc ha hba]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `h hh`. Take `⟨x, hx, rfl⟩` from `cls_surj A 0 h`. Rewrite `hh` using `[H_cls, cls_eq_zero, mem_B_zero]`. Rewrite using `[cls_eq_zero, mem_B_zero]`.

Conclude with `hs.inj 0 (hh.trans (map_zero _).symm)`. Use `exB n := by`. Introduce `y`. Take `⟨b, hb, rfl⟩` from `cls_surj B n y`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite `h` using `[H_cls, cls_eq_zero]`. Consider the cases of `n with`. Consider the case `zero`. Rewrite `h` using `[mem_B_zero]`.

Take `⟨a, ha⟩` from `((hs.exact 0) _).1 h`. Establish `da : A.d 0 a = 0` using `hs.inj 1 (by rw [i.comm, ha, hb, map_zero])`. Conclude with `⟨A.cls 0 a da, by rw [H_cls]; exact cls_congr _ _ _ _ _ _ ha⟩`. Consider the case `succ m`. Rewrite `h` using `[mem_B_succ]`.

Take `⟨c', hc'⟩` from `h`. Take `⟨b', rfl⟩` from `hs.surj m c'`. Establish `h0 : p.f (m + 1) (b - B.d m b') = 0`. Rewrite using `[map_sub, p.comm, hc', sub_self]`. Take `⟨a, ha⟩` from `((hs.exact (m + 1)) _).1 h0`.

Establish `da : A.d (m + 1) a = 0` using `hs.inj (m + 2) (by rw [i.comm, ha, map_sub, hb, B.dd, sub_zero, map_zero])`. Use `⟨A.cls (m + 1) a da, ?_⟩` and prove the remaining obligations. Rewrite using `[H_cls, cls_eq, mem_B_succ]`. Conclude with `⟨-b', by rw [map_neg, ha]; abel⟩`. Introduce and unpack `⟨x, hx⟩`.

Take `⟨a, ha, rfl⟩` from `cls_surj A n x`. Rewrite using `[← hx, H_cls, H_cls, cls_eq_zero, p_i i p hs]`. Conclude with `Submodule.zero_mem _`. Use `exC n := by`. Introduce `y`.

Take `⟨b, a, hc, ha, hb, rfl⟩` from `rep i p hs n y`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[hδ n b a hc ha hb, cls_eq_zero, mem_B_succ]`. Take `⟨a', ha'⟩` from `h`.

Establish `hz : B.d n (b - i.f n a') = 0`. Rewrite using `[map_sub, hb, ← i.comm, ha', sub_self]`. Use `⟨B.cls n (b - i.f n a') hz, ?_⟩` and prove the remaining obligations. Rewrite using `[H_cls]`. Conclude with `cls_congr _ _ _ _ _ _ (by rw [map_sub, p_i i p hs, sub_zero])`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨b'', hb'', rfl⟩` from `cls_surj B n x`. Rewrite using `[← hx, H_cls, hδ n b'' 0 _ (map_zero _) (by rw [hb'', map_zero]), cls_eq_zero]`. Conclude with `Submodule.zero_mem _`. Use `exA n := by`.

Introduce `y`. Take `⟨a, ha, rfl⟩` from `cls_surj A (n + 1) y`. Rewrite using `[H_cls, cls_eq_zero, mem_B_succ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩`.

Establish `hc : C.d n (p.f n b) = 0` using `by rw [← p.comm, hb, p_i i p hs]`. Conclude with `⟨C.cls n (p.f n b) hc, hδ n b a hc ha hb⟩`. Introduce and unpack `⟨x, hx⟩`. Take `⟨b, a', hc, ha', hb, rfl⟩` from `rep i p hs n x`. Rewrite `hx` using `[hδ n b a' hc ha' hb, cls_eq, mem_B_succ]`.

Take `⟨z, hz⟩` from `hx`. Use `⟨b - i.f n z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hb, ← i.comm, hz, map_sub, sub_sub_cancel]`.
-/
theorem les_of (hs : SES i p) (δ : ∀ n, C.H n →ₗ[R] A.H (n + 1)) (hδ : IsConn i p δ) :
    LES i p δ where
  inj := by
    rw [injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨x, hx, rfl⟩ := cls_surj A 0 h
    rw [H_cls, cls_eq_zero, mem_B_zero] at hh
    rw [cls_eq_zero, mem_B_zero]
    exact hs.inj 0 (hh.trans (map_zero _).symm)
  exB n := by
    intro y
    obtain ⟨b, hb, rfl⟩ := cls_surj B n y
    constructor
    · intro h
      rw [H_cls, cls_eq_zero] at h
      cases n with
      | zero =>
        rw [mem_B_zero] at h
        obtain ⟨a, ha⟩ := ((hs.exact 0) _).1 h
        have da : A.d 0 a = 0 := hs.inj 1 (by rw [i.comm, ha, hb, map_zero])
        exact ⟨A.cls 0 a da, by rw [H_cls]; exact cls_congr _ _ _ _ _ _ ha⟩
      | succ m =>
        rw [mem_B_succ] at h
        obtain ⟨c', hc'⟩ := h
        obtain ⟨b', rfl⟩ := hs.surj m c'
        have h0 : p.f (m + 1) (b - B.d m b') = 0 := by
          rw [map_sub, p.comm, hc', sub_self]
        obtain ⟨a, ha⟩ := ((hs.exact (m + 1)) _).1 h0
        have da : A.d (m + 1) a = 0 :=
          hs.inj (m + 2) (by rw [i.comm, ha, map_sub, hb, B.dd, sub_zero, map_zero])
        refine ⟨A.cls (m + 1) a da, ?_⟩
        rw [H_cls, cls_eq, mem_B_succ]
        exact ⟨-b', by rw [map_neg, ha]; abel⟩
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, rfl⟩ := cls_surj A n x
      rw [← hx, H_cls, H_cls, cls_eq_zero, p_i i p hs]
      exact Submodule.zero_mem _
  exC n := by
    intro y
    obtain ⟨b, a, hc, ha, hb, rfl⟩ := rep i p hs n y
    constructor
    · intro h
      rw [hδ n b a hc ha hb, cls_eq_zero, mem_B_succ] at h
      obtain ⟨a', ha'⟩ := h
      have hz : B.d n (b - i.f n a') = 0 := by
        rw [map_sub, hb, ← i.comm, ha', sub_self]
      refine ⟨B.cls n (b - i.f n a') hz, ?_⟩
      rw [H_cls]
      exact cls_congr _ _ _ _ _ _ (by rw [map_sub, p_i i p hs, sub_zero])
    · rintro ⟨x, hx⟩
      obtain ⟨b'', hb'', rfl⟩ := cls_surj B n x
      rw [← hx, H_cls, hδ n b'' 0 _ (map_zero _) (by rw [hb'', map_zero]), cls_eq_zero]
      exact Submodule.zero_mem _
  exA n := by
    intro y
    obtain ⟨a, ha, rfl⟩ := cls_surj A (n + 1) y
    rw [H_cls, cls_eq_zero, mem_B_succ]
    constructor
    · rintro ⟨b, hb⟩
      have hc : C.d n (p.f n b) = 0 := by rw [← p.comm, hb, p_i i p hs]
      exact ⟨C.cls n (p.f n b) hc, hδ n b a hc ha hb⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, a', hc, ha', hb, rfl⟩ := rep i p hs n x
      rw [hδ n b a' hc ha' hb, cls_eq, mem_B_succ] at hx
      obtain ⟨z, hz⟩ := hx
      refine ⟨b - i.f n z, ?_⟩
      rw [map_sub, hb, ← i.comm, hz, map_sub, sub_sub_cancel]

end LongExactSequenceMaps

/- English proof (translation)
Introduce `R _ A B C i p hs`. Conclude with `⟨⟨LongExactSequenceMaps.conn i p hs, LongExactSequenceMaps.conn_isConn i p hs, LongExactSequenceMaps.les_of i p hs _ (LongExactSequenceMaps.conn_isConn i p hs)⟩, fun δ δ' h h' => LongExactSequenceMaps.uniq i p hs δ δ' h h'⟩`.
-/
theorem lES_holds : LESStatement.{u} := by
  intro R _ A B C i p hs
  exact ⟨⟨LongExactSequenceMaps.conn i p hs, LongExactSequenceMaps.conn_isConn i p hs,
    LongExactSequenceMaps.les_of i p hs _ (LongExactSequenceMaps.conn_isConn i p hs)⟩,
    fun δ δ' h h' => LongExactSequenceMaps.uniq i p hs δ δ' h h'⟩

/- English proof (translation)
Introduce `R _ A B C A' B' C' i p i' p' α β γ δ δ' hs hs' hiα hpγ hδ hδ' n x`. Take `⟨b, a, hc, ha, hba, rfl⟩` from `LongExactSequenceMaps.rep i p hs n x`. Establish `hc' : C'.d n (p'.f n (β.f n b)) = 0` using `by rw [← hpγ, ← γ.comm, hc, map_zero]`. Establish `hba' : B'.d n (β.f n b) = i'.f (n + 1) (α.f (n + 1) a)` using `by rw [← β.comm, hba, hiα]`. Rewrite using `[hδ n b a hc ha hba, LongExactSequenceMaps.H_cls, LongExactSequenceMaps.H_cls, LongExactSequenceMaps.cls_congr C' n _ _ _ hc' (hpγ n b)]`.

Conclude with `hδ' n (β.f n b) (α.f (n + 1) a) hc' _ hba'`.
-/
theorem connNat_holds : ConnNatStatement.{u} := by
  intro R _ A B C A' B' C' i p i' p' α β γ δ δ' hs hs' hiα hpγ hδ hδ' n x
  obtain ⟨b, a, hc, ha, hba, rfl⟩ := LongExactSequenceMaps.rep i p hs n x
  have hc' : C'.d n (p'.f n (β.f n b)) = 0 := by rw [← hpγ, ← γ.comm, hc, map_zero]
  have hba' : B'.d n (β.f n b) = i'.f (n + 1) (α.f (n + 1) a) := by rw [← β.comm, hba, hiα]
  rw [hδ n b a hc ha hba, LongExactSequenceMaps.H_cls, LongExactSequenceMaps.H_cls, LongExactSequenceMaps.cls_congr C' n _ _ _ hc' (hpγ n b)]
  exact hδ' n (β.f n b) (α.f (n + 1) a) hc' _ hba'

end ReciprocityTheory.Coh
