import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureMulVOfFinrankEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section Abstract

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨fun s hs => hs, fun s hs => rfl⟩`. Consider the case `succ m ih`. Take `⟨ih1, ih2⟩` from `ih`. Use `⟨fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ', End.mul_apply]`. Conclude with `hΦ _ (ih1 s hs)`. Rewrite using `[pow_succ', pow_succ', End.mul_apply, End.mul_apply]`. Establish `e : (T ^ m) ⟨s, hSD hs⟩ = ⟨(Φ ^ m) s, hSD (ih1 s hs)⟩` using `Subtype.ext (ih2 s hs)`. Rewrite using `[e, hT _ (ih1 s hs)]`.
-/
private theorem pow_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (m : ℕ) :
    (∀ s ∈ S, (Φ ^ m) s ∈ S) ∧ ∀ s (hs : s ∈ S), (((T ^ m) ⟨s, hSD hs⟩ : D) : M) = (Φ ^ m) s := by
  induction m with
  | zero => exact ⟨fun s hs => hs, fun s hs => rfl⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [pow_succ', End.mul_apply]
      exact hΦ _ (ih1 s hs)
    · rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply]
      have e : (T ^ m) ⟨s, hSD hs⟩ = ⟨(Φ ^ m) s, hSD (ih1 s hs)⟩ := Subtype.ext (ih2 s hs)
      rw [e, hT _ (ih1 s hs)]

/- English proof (translation)
Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Use `⟨fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `add_mem (hp.1 s hs) (hq.1 s hs)`.

Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp.2 s hs, hq.2 s hs]`. Consider the case `monomial n a`. Take `⟨h1, h2⟩` from `pow_restr D S hSD T Φ hΦ hT n`. Use `⟨fun s hs => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_monomial, End.mul_apply, Module.algebraMap_end_apply]`.

Conclude with `S.smul_mem a (h1 s hs)`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.aeval_monomial, End.mul_apply, End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, h2 s hs]`.
-/
private theorem aeval_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) :
    (∀ s ∈ S, Polynomial.aeval Φ Q s ∈ S) ∧
      ∀ s (hs : s ∈ S), ((Polynomial.aeval T Q ⟨s, hSD hs⟩ : D) : M) = Polynomial.aeval Φ Q s := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [map_add, LinearMap.add_apply]
      exact add_mem (hp.1 s hs) (hq.1 s hs)
    · rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp.2 s hs, hq.2 s hs]
  | monomial n a =>
    obtain ⟨h1, h2⟩ := pow_restr D S hSD T Φ hΦ hT n
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [Polynomial.aeval_monomial, End.mul_apply, Module.algebraMap_end_apply]
      exact S.smul_mem a (h1 s hs)
    · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, End.mul_apply, End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, h2 s hs]

/- English proof (translation)
Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_left hq`. Consider the case `monomial n a`. Rewrite using `[Polynomial.aeval_monomial]`.

Conclude with `Commute.mul_left (show Commute _ m from Algebra.commutes a m) (h.pow_left n)`.
-/
private theorem aeval_commute {D : Type} [AddCommGroup D] [Module L D] (T m : End L D) (h : Commute T m)
    (Q : Polynomial L) : Commute (Polynomial.aeval T Q) m := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact Commute.mul_left (show Commute _ m from Algebra.commutes a m) (h.pow_left n)

/- English proof (translation)
Take `⟨a1, a2⟩` from `aeval_restr D S hSD T Φ hΦ hT Q`. Take `⟨-, b2⟩` from `pow_restr D S hSD _ _ a1 a2 N`. Establish `hkill : ∀ s (hs' : s ∈ S), (Polynomial.aeval T Q ^ N) ⟨s, hSD hs'⟩ = 0`. Introduce `s hs'`. Use `Subtype.ext ?_` and prove the remaining obligations.

Rewrite using `[b2 s hs']`. Conclude with `hN s hs'`. Establish `hcomm : ∀ c, Commute (Polynomial.aeval T Q ^ N) (m c)` using `fun c => Commute.pow_left (aeval_commute _ _ (hc c) Q) N`. Establish `key : ∀ y, y ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s} → ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0`. Introduce `y hy`.

Use `AddSubgroup.closure_induction (p := fun y _ => ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0) ?_ ⟨zero_mem _, map_zero _⟩ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨c, s, hs', rfl⟩`. Establish `e : mV c s = ((m c ⟨s, hSD hs'⟩ : D) : M)` using `(hm c ⟨s, hSD hs'⟩).symm`. Use `⟨e ▸ (m c ⟨s, hSD hs'⟩).2, ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun (hcomm c).eq ⟨s, hSD hs'⟩`.

Rewrite `h1` using `[End.mul_apply, End.mul_apply, hkill s hs', map_zero]`. Establish `h2 : (⟨mV c s, e ▸ (m c ⟨s, hSD hs'⟩).2⟩ : D) = m c ⟨s, hSD hs'⟩` using `Subtype.ext e`. Rewrite using `[h2]`. Conclude with `h1`. Introduce and unpack `a b _ _ ⟨ha, ea⟩ ⟨hb, eb⟩`.

Use `⟨add_mem ha hb, ?_⟩` and prove the remaining obligations. Use `map_add (Polynomial.aeval T Q ^ N) ⟨a, ha⟩ ⟨b, hb⟩` as an intermediate fact. Rewrite `this` using `[ea, eb, add_zero]`. Conclude with `this`. Introduce and unpack `a _ ⟨ha, ea⟩`.

Use `⟨neg_mem ha, ?_⟩` and prove the remaining obligations. Use `map_neg (Polynomial.aeval T Q ^ N) ⟨a, ha⟩` as an intermediate fact. Rewrite `this` using `[ea, neg_zero]`. Conclude with `this`. Use `⟨N, LinearMap.ext fun x => ?_⟩` and prove the remaining obligations.

Take `⟨hy, e⟩` from `key x.1 (hcl x)`. Conclude with `e`.
-/
private theorem nil_abs {U : Type} (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) (N : ℕ)
    (hN : ∀ s ∈ S, (Polynomial.aeval Φ Q ^ N) s = 0) (m : U → End L D) (mV : U → End L M)
    (hm : ∀ c (x : D), ((m c x : D) : M) = mV c x) (hc : ∀ c, T * m c = m c * T)
    (hcl : ∀ x : D, (x : M) ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s}) :
    IsNilpotent (Polynomial.aeval T Q) := by
  obtain ⟨a1, a2⟩ := aeval_restr D S hSD T Φ hΦ hT Q
  obtain ⟨-, b2⟩ := pow_restr D S hSD _ _ a1 a2 N
  have hkill : ∀ s (hs' : s ∈ S), (Polynomial.aeval T Q ^ N) ⟨s, hSD hs'⟩ = 0 := by
    intro s hs'
    refine Subtype.ext ?_
    rw [b2 s hs']
    exact hN s hs'
  have hcomm : ∀ c, Commute (Polynomial.aeval T Q ^ N) (m c) := fun c =>
    Commute.pow_left (aeval_commute _ _ (hc c) Q) N
  have key : ∀ y, y ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s} →
      ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0 := by
    intro y hy
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0)
      ?_ ⟨zero_mem _, map_zero _⟩ ?_ ?_ hy
    · rintro _ ⟨c, s, hs', rfl⟩
      have e : mV c s = ((m c ⟨s, hSD hs'⟩ : D) : M) := (hm c ⟨s, hSD hs'⟩).symm
      refine ⟨e ▸ (m c ⟨s, hSD hs'⟩).2, ?_⟩
      have h1 := LinearMap.congr_fun (hcomm c).eq ⟨s, hSD hs'⟩
      rw [End.mul_apply, End.mul_apply, hkill s hs', map_zero] at h1
      have h2 : (⟨mV c s, e ▸ (m c ⟨s, hSD hs'⟩).2⟩ : D) = m c ⟨s, hSD hs'⟩ := Subtype.ext e
      rw [h2]; exact h1
    · rintro a b _ _ ⟨ha, ea⟩ ⟨hb, eb⟩
      refine ⟨add_mem ha hb, ?_⟩
      have := map_add (Polynomial.aeval T Q ^ N) ⟨a, ha⟩ ⟨b, hb⟩
      rw [ea, eb, add_zero] at this
      exact this
    · rintro a _ ⟨ha, ea⟩
      refine ⟨neg_mem ha, ?_⟩
      have := map_neg (Polynomial.aeval T Q ^ N) ⟨a, ha⟩
      rw [ea, neg_zero] at this
      exact this
  refine ⟨N, LinearMap.ext fun x => ?_⟩
  obtain ⟨hy, e⟩ := key x.1 (hcl x)
  exact e

end Abstract

/- English proof (translation)
Introduce `l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV hs Q hN g hg`. Use `haveI := hV.finite`. Take `⟨N, hN⟩` from `hN`. Establish `hSD : Dst P ρ ≤ Dpst P ρ` using `fun s hs => (mem_Dpst P ρ).mpr ⟨Bw.Kw, fun g _ => (mem_Dst P ρ).mp hs g⟩`. Establish `hΦ : onPer (ψSt P (resDeg l w)) ↥LL.1 V = phiV P ↥LL.1 V ^ resDeg l w`.

Express the relevant statement in the definitionally equal form `onB P ↥LL.1 V ((phiSt P).toLinearMap ^ resDeg l w) = _`. Rewrite using `[map_pow]`. Both sides reduce to the same expression. Establish `hpow : ∀ (m : ℕ) (x : ↥(Dpst P ρ)), (((phiD P ρ ^ m) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P ↥LL.1 V ^ m) x`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `succ m ih`. Introduce `x`.

Rewrite using `[pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih]`. Establish `hst : ∀ (m : ℕ), ∀ s ∈ Dst P ρ, (phiV P ↥LL.1 V ^ m) s ∈ Dst P ρ`. Introduce `m s hs'`. Use `(mem_Dst P ρ).mpr fun k => ?_` and prove the remaining obligations. Establish `hc : Commute (phiV P ↥LL.1 V ^ m) (stRep P ρ k)` using `Commute.pow_left (phiV_stRep P ρ k) m`.

Use `LinearMap.congr_fun hc.eq s` as an intermediate fact. Rewrite `this` using `[End.mul_apply, End.mul_apply, (mem_Dst P ρ).mp hs' k]`. Conclude with `this.symm`. Establish `hW : ∀ s (hs' : s ∈ Dst P ρ), ((weilD Bw h P ρ g ⟨s, hSD hs'⟩ : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = onPer (ψSt P (resDeg l w)) ↥LL.1 V s`. Introduce `s hs'`.

Establish `e : -alpha l g = ((resDeg l w : ℕ) : ℤ)` using `by rw [alpha, hg]; ring`. Rewrite using `[weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD, hpow, hΦ]`. Conclude with `(mem_Dst P ρ).mp (hst _ s hs') _`. Establish `hΦS : ∀ s ∈ Dst P ρ, onPer (ψSt P (resDeg l w)) ↥LL.1 V s ∈ Dst P ρ`. Introduce `s hs'`.

Rewrite using `[hΦ]`. Conclude with `hst _ s hs'`. Establish `hcl` using `mem_closure_mulV_of_finrank_eq l P Bw.Kw LL V ρ hV (Dst P ρ) le_rfl (fun c hc x hx => (mem_Dst P ρ).mpr fun k => by`. Rewrite using `[← Module.End.mul_apply, stRep_mulV P ρ k c c (mem_GK.mp k.2 _ hc), Module.End.mul_apply, (mem_Dst P ρ).mp hx k]) hs`. Conclude with `nil_abs (Dpst P ρ) (Dst P ρ) hSD (weilD Bw h P ρ g) (onPer (ψSt P (resDeg l w)) ↥LL.1 V) hΦS hW Q N (fun s hs' => hN s hs') (mulD P ρ) (mulV P ↥LL.1 V) (fun _ _ => rfl) (weilD_mulD Bw h P ρ hj g) (fun x => hcl x.1 x.2)`.
-/
theorem UpperTheory.Gal.crystallineComparison.nilWeil_of :
    NilWeil := by
  intro l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV hs Q hN g hg
  haveI := hV.finite
  obtain ⟨N, hN⟩ := hN
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs =>
    (mem_Dpst P ρ).mpr ⟨Bw.Kw, fun g _ => (mem_Dst P ρ).mp hs g⟩
  have hΦ : onPer (ψSt P (resDeg l w)) ↥LL.1 V = phiV P ↥LL.1 V ^ resDeg l w := by
    change onB P ↥LL.1 V ((phiSt P).toLinearMap ^ resDeg l w) = _
    rw [map_pow]; rfl
  have hpow : ∀ (m : ℕ) (x : ↥(Dpst P ρ)),
      (((phiD P ρ ^ m) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P ↥LL.1 V ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih]
  have hst : ∀ (m : ℕ), ∀ s ∈ Dst P ρ, (phiV P ↥LL.1 V ^ m) s ∈ Dst P ρ := by
    intro m s hs'
    refine (mem_Dst P ρ).mpr fun k => ?_
    have hc : Commute (phiV P ↥LL.1 V ^ m) (stRep P ρ k) := Commute.pow_left (phiV_stRep P ρ k) m
    have := LinearMap.congr_fun hc.eq s
    rw [End.mul_apply, End.mul_apply, (mem_Dst P ρ).mp hs' k] at this
    exact this.symm
  have hW : ∀ s (hs' : s ∈ Dst P ρ), ((weilD Bw h P ρ g ⟨s, hSD hs'⟩ : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      onPer (ψSt P (resDeg l w)) ↥LL.1 V s := by
    intro s hs'
    have e : -alpha l g = ((resDeg l w : ℕ) : ℤ) := by rw [alpha, hg]; ring
    rw [weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD, hpow, hΦ]
    exact (mem_Dst P ρ).mp (hst _ s hs') _
  have hΦS : ∀ s ∈ Dst P ρ, onPer (ψSt P (resDeg l w)) ↥LL.1 V s ∈ Dst P ρ := by
    intro s hs'
    rw [hΦ]; exact hst _ s hs'
  have hcl := mem_closure_mulV_of_finrank_eq l P Bw.Kw LL V ρ hV (Dst P ρ) le_rfl
    (fun c hc x hx => (mem_Dst P ρ).mpr fun k => by
      rw [← Module.End.mul_apply, stRep_mulV P ρ k c c (mem_GK.mp k.2 _ hc), Module.End.mul_apply,
        (mem_Dst P ρ).mp hx k]) hs
  exact nil_abs (Dpst P ρ) (Dst P ρ) hSD (weilD Bw h P ρ g) (onPer (ψSt P (resDeg l w)) ↥LL.1 V) hΦS hW Q N
    (fun s hs' => hN s hs') (mulD P ρ) (mulV P ↥LL.1 V) (fun _ _ => rfl) (weilD_mulD Bw h P ρ hj g) (fun x => hcl x.1 x.2)
