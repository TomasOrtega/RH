import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.ContFn

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]`.
-/
theorem smod_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    SModEq ((Ideal.span {a}) ^ n • ⊤ : Submodule R R) x y ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) {Γ : Type} [TopologicalSpace Γ]

/- English proof (translation)
The claim follows from `A.tf`.
-/
theorem pi_nzd : A.pi ∈ nonZeroDivisors A.A := A.tf

/- English proof (translation)
Use `forall_congr' fun k => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsLocallyConstant (fun γ => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (f γ)) ↔ _`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Use `forall_congr' fun γ => Filter.eventually_congr (Filter.Eventually.of_forall fun γ' => ?_)` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`.
-/
theorem mem_contR_iff (f : Γ → A.A) :
    f ∈ A.contR Γ ↔ ∀ k : ℕ, ∀ γ : Γ, ∀ᶠ γ' in nhds γ, A.pi ^ k ∣ f γ' - f γ := by
  refine forall_congr' fun k => ?_
  change IsLocallyConstant (fun γ => Ideal.Quotient.mk (Ideal.span {A.pi ^ k}) (f γ)) ↔ _
  rw [IsLocallyConstant.iff_eventually_eq]
  refine forall_congr' fun γ => Filter.eventually_congr (Filter.Eventually.of_forall fun γ' => ?_)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hk : A.pi ^ k ∈ nonZeroDivisors A.A` using `pow_mem (pi_nzd A) k`. Use `mem_nonZeroDivisors_iff_left.1 hk (a - A.pi ^ j * c) (by rw [mul_sub, hc, pow_add]; ring)` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem pow_cancel {k j : ℕ} {a : A.A} (h : A.pi ^ (k + j) ∣ A.pi ^ k * a) : A.pi ^ j ∣ a := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have hk : A.pi ^ k ∈ nonZeroDivisors A.A := pow_mem (pi_nzd A) k
  have := mem_nonZeroDivisors_iff_left.1 hk (a - A.pi ^ j * c) (by rw [mul_sub, hc, pow_add]; ring)
  exact sub_eq_zero.1 this

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Take `⟨c', rfl⟩` from `A.frob_bijective.2 c`. Use `⟨c', A.frob_bijective.1 ?_⟩` and prove the remaining obligations. Rewrite using `[hc, map_mul]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `A.pi ^ (l * k) = (A.pi ^ k) ^ l`. Rewrite using `[← pow_mul, mul_comm]`.
-/
theorem frob_dvd {k : ℕ} {d : A.A} (h : A.pi ^ (l * k) ∣ A.frob d) : A.pi ^ k ∣ d := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', rfl⟩ := A.frob_bijective.2 c
  refine ⟨c', A.frob_bijective.1 ?_⟩
  rw [hc, map_mul]
  congr 1
  change A.pi ^ (l * k) = (A.pi ^ k) ^ l
  rw [← pow_mul, mul_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem val_pow_apply (f : A.contR Γ) (k : ℕ) (γ : Γ) : (f ^ k).1 γ = f.1 γ ^ k := by
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ γ`. Use `⟨g.1 γ, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(A.contC Γ A.pi ^ k).1 γ * g.1 γ = _`. Rewrite using `[val_pow_apply]`.

Both sides reduce to the same expression. Introduce `h choose g hg using h`. Establish `hg' : g ∈ A.contR Γ` using `(mem_contR_iff A g).2 fun j γ => by filter_upwards [(mem_contR_iff A f.1).1 f.2 (k + j) γ] with γ' hγ'`. Rewrite `hγ'` using `[hg γ', hg γ, ← mul_sub]`. Conclude with `pow_cancel A hγ'`.

Use `⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩` and prove the remaining obligations. Use `(hg γ).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (A.contC Γ A.pi ^ k).1 γ * g γ`. Rewrite using `[val_pow_apply]`. Both sides reduce to the same expression.
-/
theorem dvd_iff (k : ℕ) (f : A.contR Γ) : A.contC Γ A.pi ^ k ∣ f ↔ ∀ γ, A.pi ^ k ∣ f.1 γ := by
  constructor
  · rintro ⟨g, rfl⟩ γ
    refine ⟨g.1 γ, ?_⟩
    change (A.contC Γ A.pi ^ k).1 γ * g.1 γ = _
    rw [val_pow_apply]
    rfl
  · intro h
    choose g hg using h
    have hg' : g ∈ A.contR Γ := (mem_contR_iff A g).2 fun j γ => by
      filter_upwards [(mem_contR_iff A f.1).1 f.2 (k + j) γ] with γ' hγ'
      rw [hg γ', hg γ, ← mul_sub] at hγ'
      exact pow_cancel A hγ'
    refine ⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩
    refine (hg γ).trans ?_
    change _ = (A.contC Γ A.pi ^ k).1 γ * g γ
    rw [val_pow_apply]
    rfl

/- English proof (translation)
Use `⟨⟨fun x y h => ?_, fun f => ?_⟩⟩` and prove the remaining obligations. Use `Subtype.ext (funext fun γ => A.frob_bijective.1 ?_)` and prove the remaining obligations. Establish `e` using `congrFun (congrArg Subtype.val h) γ`. Express the relevant statement in the definitionally equal form `(x ^ l).1 γ = (y ^ l).1 γ at e`. Rewrite `e` using `[val_pow_apply, val_pow_apply]`.

Conclude with `e`. Use `choose g hg using fun γ => A.frob_bijective.2 (f.1 γ)`. Establish `hg' : g ∈ A.contR Γ` using `(mem_contR_iff A g).2 fun k γ => by filter_upwards [(mem_contR_iff A f.1).1 f.2 (l * k) γ] with γ' hγ'`. Use `frob_dvd A ?_` and prove the remaining obligations. Rewrite using `[map_sub, hg γ', hg γ]`.

Conclude with `hγ'`. Use `⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((⟨g, hg'⟩ : A.contR Γ) ^ l).1 γ = _`. Rewrite using `[val_pow_apply]`. Conclude with `hg γ`.
-/
theorem perfect : PerfectRing (A.contR Γ) l := by
  refine ⟨⟨fun x y h => ?_, fun f => ?_⟩⟩
  · refine Subtype.ext (funext fun γ => A.frob_bijective.1 ?_)
    have e := congrFun (congrArg Subtype.val h) γ
    change (x ^ l).1 γ = (y ^ l).1 γ at e
    rw [val_pow_apply, val_pow_apply] at e
    exact e
  · choose g hg using fun γ => A.frob_bijective.2 (f.1 γ)
    have hg' : g ∈ A.contR Γ := (mem_contR_iff A g).2 fun k γ => by
      filter_upwards [(mem_contR_iff A f.1).1 f.2 (l * k) γ] with γ' hγ'
      refine frob_dvd A ?_
      rw [map_sub, hg γ', hg γ]
      exact hγ'
    refine ⟨⟨g, hg'⟩, Subtype.ext (funext fun γ => ?_)⟩
    change ((⟨g, hg'⟩ : A.contR Γ) ^ l).1 γ = _
    rw [val_pow_apply]
    exact hg γ

/- English proof (translation)
Establish `hc : IsAdicComplete (Ideal.span {A.pi}) A.A` using `A.compl`. Establish `h1 : IsHausdorff (Ideal.span {A.contC Γ A.pi}) (A.contR Γ)` using `⟨fun x hx => by`. Use `Subtype.ext (funext fun γ => ?_)` and prove the remaining obligations. Use `hc.toIsHausdorff.haus' (x.1 γ) fun n => (smod_iff _ _ _ _).2 ?_` and prove the remaining obligations. Use `(dvd_iff A n x).1 (by simpa using (smod_iff _ _ _ _).1 (hx n)) γ` as an intermediate fact.

Simplify using `using this⟩`. Establish `h2 : IsPrecomplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ)` using `⟨fun f hf => by`. Establish `hp : ∀ m n, m ≤ n → ∀ γ, A.pi ^ m ∣ (f m).1 γ - (f n).1 γ` using `fun m n h γ => (dvd_iff A m (f m - f n)).1 ((smod_iff _ _ _ _).1 (hf h)) γ`. Use `choose L hL using fun γ => hc.toIsPrecomplete.prec (f := fun n => (f n).1 γ) fun {m n} h => (smod_iff _ _ _ _).2 (hp m n h γ)`. Establish `hL' : ∀ n γ, A.pi ^ n ∣ (f n).1 γ - L γ` using `fun n γ => (smod_iff _ _ _ _).1 (hL γ n)`.

Establish `hLm : L ∈ A.contR Γ` using `(mem_contR_iff A L).2 fun k γ => by filter_upwards [(mem_contR_iff A (f k).1).1 (f k).2 k γ] with γ' h`. Establish `e : L γ' - L γ = ((f k).1 γ' - (f k).1 γ) - ((f k).1 γ' - L γ') + ((f k).1 γ - L γ)` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add (dvd_sub h (hL' k γ')) (hL' k γ)`. Conclude with `⟨⟨L, hLm⟩, fun n => (smod_iff _ _ _ _).2 ((dvd_iff A n _).2 fun γ => hL' n γ)⟩⟩`.

Conclude with `{ toIsHausdorff := h1, toIsPrecomplete := h2 }`.
-/
theorem complete : IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := by
  have hc : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  have h1 : IsHausdorff (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := ⟨fun x hx => by
    refine Subtype.ext (funext fun γ => ?_)
    refine hc.toIsHausdorff.haus' (x.1 γ) fun n => (smod_iff _ _ _ _).2 ?_
    have := (dvd_iff A n x).1 (by simpa using (smod_iff _ _ _ _).1 (hx n)) γ
    simpa using this⟩
  have h2 : IsPrecomplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) := ⟨fun f hf => by
    have hp : ∀ m n, m ≤ n → ∀ γ, A.pi ^ m ∣ (f m).1 γ - (f n).1 γ := fun m n h γ =>
      (dvd_iff A m (f m - f n)).1 ((smod_iff _ _ _ _).1 (hf h)) γ
    choose L hL using fun γ => hc.toIsPrecomplete.prec (f := fun n => (f n).1 γ)
      fun {m n} h => (smod_iff _ _ _ _).2 (hp m n h γ)
    have hL' : ∀ n γ, A.pi ^ n ∣ (f n).1 γ - L γ := fun n γ => (smod_iff _ _ _ _).1 (hL γ n)
    have hLm : L ∈ A.contR Γ := (mem_contR_iff A L).2 fun k γ => by
      filter_upwards [(mem_contR_iff A (f k).1).1 (f k).2 k γ] with γ' h
      have e : L γ' - L γ = ((f k).1 γ' - (f k).1 γ) - ((f k).1 γ' - L γ') + ((f k).1 γ - L γ) := by ring
      rw [e]
      exact dvd_add (dvd_sub h (hL' k γ')) (hL' k γ)
    exact ⟨⟨L, hLm⟩, fun n => (smod_iff _ _ _ _).2 ((dvd_iff A n _).2 fun γ => hL' n γ)⟩⟩
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }

/- English proof (translation)
The claim follows from `mem_nonZeroDivisors_iff_left.2 fun x hx => Subtype.ext (funext fun γ => mem_nonZeroDivisors_iff_left.1 (pi_nzd A) (x.1 γ) (congrFun (congrArg Subtype.val hx) γ))`.
-/
theorem contC_pi_nzd : A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) :=
  mem_nonZeroDivisors_iff_left.2 fun x hx => Subtype.ext (funext fun γ =>
    mem_nonZeroDivisors_iff_left.1 (pi_nzd A) (x.1 γ) (congrFun (congrArg Subtype.val hx) γ))

/- English proof (translation)
Introduce `A Γ _` and use `⟨perfect A, complete A, contC_pi_nzd A, fun k f => by simp only [Ideal.mem_span_singleton] exact dvd_iff A k f⟩`.
-/
theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (Γ : Type) [TopologicalSpace Γ],
    PerfectRing (A.contR Γ) l ∧ IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) ∧
      A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) ∧
      ∀ (k : ℕ) (f : A.contR Γ), f ∈ Ideal.span {A.contC Γ A.pi ^ k} ↔
        ∀ γ, f.1 γ ∈ Ideal.span {A.pi ^ k} := fun A Γ _ =>
  ⟨perfect A, complete A, contC_pi_nzd A, fun k f => by
    simp only [Ideal.mem_span_singleton]
    exact dvd_iff A k f⟩

end GlobalTheory.CompanionTheory.ContFn
