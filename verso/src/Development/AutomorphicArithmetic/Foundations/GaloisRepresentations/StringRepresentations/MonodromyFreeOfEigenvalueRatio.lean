import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.ScalarOfCharpoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleWdEigenEqualNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedRestriction

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.GalN

section Lin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hd` using `(End.eigenspaces_iSupIndep f).disjoint_biSup_biSup (s := {α | ‖α‖ = r}) (t := {α | ‖α‖ = r'}) (Set.disjoint_left.2 fun α a b => hne (a.symm.trans b))`. Conclude with `hv (Submodule.disjoint_def.1 hd v h1 h2)`.
-/
theorem absSpace_disj {f : End ℂ V} {r r' : ℝ} {v : V} (h1 : v ∈ absSpace f r) (h2 : v ∈ absSpace f r') (hv : v ≠ 0) :
    r = r' := by
  by_contra hne
  have hd := (End.eigenspaces_iSupIndep f).disjoint_biSup_biSup (s := {α | ‖α‖ = r}) (t := {α | ‖α‖ = r'})
    (Set.disjoint_left.2 fun α a b => hne (a.symm.trans b))
  exact hv (Submodule.disjoint_def.1 hd v h1 h2)

/- English proof (translation)
Use `(iSup₂_le fun α hα u hu => ?_ : absSpace (c • f) r ≤ absSpace f (r / ‖c‖)) hv` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem (α / c) (Submodule.mem_iSup_of_mem (by rw [norm_div, hα]) ?_)` and prove the remaining obligations. Rewrite `hu`, the goal using `[End.mem_eigenspace_iff]`. Rewrite `hu` using `[LinearMap.smul_apply]`. Rewrite using `[div_eq_inv_mul, mul_smul, ← hu, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem absSpace_smul {f : End ℂ V} {c : ℂ} (hc : c ≠ 0) {r : ℝ} {v : V} (hv : v ∈ absSpace (c • f) r) :
    v ∈ absSpace f (r / ‖c‖) := by
  refine (iSup₂_le fun α hα u hu => ?_ : absSpace (c • f) r ≤ absSpace f (r / ‖c‖)) hv
  refine Submodule.mem_iSup_of_mem (α / c) (Submodule.mem_iSup_of_mem (by rw [norm_div, hα]) ?_)
  rw [End.mem_eigenspace_iff] at hu ⊢
  rw [LinearMap.smul_apply] at hu
  rw [div_eq_inv_mul, mul_smul, ← hu, smul_smul, inv_mul_cancel₀ hc, one_smul]

/- English proof (translation)
Use `(iSup₂_le fun α hα u hu => ?_ : absSpace f r ≤ (absSpace f (‖c‖ * r)).comap N) hv` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem (c * α) (Submodule.mem_iSup_of_mem (by rw [norm_mul, hα]) ?_)` and prove the remaining obligations. Rewrite `hu`, the goal using `[End.mem_eigenspace_iff]`. Rewrite using `[hN, hu, map_smul, smul_smul]`.
-/
theorem absSpace_shift {f N : End ℂ V} {c : ℂ} (hN : ∀ v, f (N v) = c • N (f v)) {r : ℝ} {v : V} (hv : v ∈ absSpace f r) :
    N v ∈ absSpace f (‖c‖ * r) := by
  refine (iSup₂_le fun α hα u hu => ?_ : absSpace f r ≤ (absSpace f (‖c‖ * r)).comap N) hv
  refine Submodule.mem_iSup_of_mem (c * α) (Submodule.mem_iSup_of_mem (by rw [norm_mul, hα]) ?_)
  rw [End.mem_eigenspace_iff] at hu ⊢
  rw [hN, hu, map_smul, smul_smul]
end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def EV (a : WDRep h V) (χ : ↥(Ine (F := E) A) → ℂ) (v : V) : Prop := ∀ s, a.ρ (ineIncl h s) v = χ s • v

def Win (a : WDRep h V) (S : Set ℝ) : Prop :=
  ∀ χ, (∀ v, EV a χ v → a.N v = 0) → ∀ r v, EV a χ v → v ∈ absSpace (a.ρ (frob h)) r → v ≠ 0 → r ∈ S

/- English proof (translation)
Take `⟨e, e1, e2⟩` from `e`. Introduce `χ h0 r v hv hr hv0`. Use `hb χ (fun u hu => ?_) r (e v) (fun s => by rw [← e1, hv s, map_smul]) (map_absSpace_le e.toLinearMap (fun x => e1 _ x) r ⟨v, hr, rfl⟩) (e.map_ne_zero_iff.2 hv0)` and prove the remaining obligations. Take `⟨u, rfl⟩` from `e.surjective u`. Rewrite using `[← e2, h0 u fun s => e.injective (by rw [e1, hu s, map_smul]), map_zero]`.
-/
theorem Win.iso {a : WDRep h V} {b : WDRep h V'} {S : Set ℝ} (e : a.Iso b) (hb : Win b S) : Win a S := by
  obtain ⟨e, e1, e2⟩ := e
  intro χ h0 r v hv hr hv0
  refine hb χ (fun u hu => ?_) r (e v) (fun s => by rw [← e1, hv s, map_smul])
    (map_absSpace_le e.toLinearMap (fun x => e1 _ x) r ⟨v, hr, rfl⟩) (e.map_ne_zero_iff.2 hv0)
  obtain ⟨u, rfl⟩ := e.surjective u
  rw [← e2, h0 u fun s => e.injective (by rw [e1, hu s, map_smul]), map_zero]

/- English proof (translation)
Introduce `χ h0 r v hv hr hv0`. Establish `hr'` using `(mem_absSpace_prodMap (a.ρ (frob h)) (b.ρ (frob h)) r v).1 hr`. Distinguish the cases in `h1 : v.1 = 0`. Use `hb χ (fun u hu => ?_) r v.2 (fun s => congrArg Prod.snd (hv s)) hr'.2 fun h2 => hv0 (Prod.ext h1 h2)` and prove the remaining obligations. Conclude with `congrArg Prod.snd (h0 (0, u) fun s => Prod.ext (by simp) (hu s))`.

Use `ha χ (fun u hu => ?_) r v.1 (fun s => congrArg Prod.fst (hv s)) hr'.1 h1` and prove the remaining obligations. Conclude with `congrArg Prod.fst (h0 (u, 0) fun s => Prod.ext (hu s) (by simp))`.
-/
theorem Win.sum {a : WDRep h V} {b : WDRep h V'} {S : Set ℝ} (ha : Win a S) (hb : Win b S) : Win (a.sum b) S := by
  intro χ h0 r v hv hr hv0
  have hr' := (mem_absSpace_prodMap (a.ρ (frob h)) (b.ρ (frob h)) r v).1 hr
  by_cases h1 : v.1 = 0
  · refine hb χ (fun u hu => ?_) r v.2 (fun s => congrArg Prod.snd (hv s)) hr'.2 fun h2 => hv0 (Prod.ext h1 h2)
    exact congrArg Prod.snd (h0 (0, u) fun s => Prod.ext (by simp) (hu s))
  · refine ha χ (fun u hu => ?_) r v.1 (fun s => congrArg Prod.fst (hv s)) hr'.1 h1
    exact congrArg Prod.fst (h0 (u, 0) fun s => Prod.ext (hu s) (by simp))

/- English proof (translation)
Introduce `χ h0 r v hv hr hv0` and use `hS (ha χ h0 r v hv hr hv0)`.
-/
theorem Win.mono {a : WDRep h V} {S T : Set ℝ} (ha : Win a S) (hS : S ⊆ T) : Win a T :=
  fun χ h0 r v hv hr hv0 => hS (ha χ h0 r v hv hr hv0)

/- English proof (translation)
Introduce `χ h0 r v hv hr hv0`. Establish `e : ∀ u, EV (a.tw s) χ u ↔ EV a χ u` using `fun u => by simp [EV]`. Establish `e2 : (a.tw s).ρ (frob h) = (qPow w s : ℂ) • a.ρ (frob h)` using `by simp [deg_frob]`. Rewrite `hr` using `[e2]`. Use `ha χ (fun u hu => h0 u ((e u).2 hu)) _ v ((e v).1 hv) (absSpace_smul (qPow w s).ne_zero hr) hv0` as an intermediate fact.

Rewrite `this` using `[norm_qPow]`. Then use the resulting hypothesis.
-/
theorem Win.tw {a : WDRep h V} {S : Set ℝ} (ha : Win a S) (s : ℝ) :
    Win (a.tw s) {r | r / ((normV w : ℕ) : ℝ) ^ s ∈ S} := by
  intro χ h0 r v hv hr hv0
  have e : ∀ u, EV (a.tw s) χ u ↔ EV a χ u := fun u => by simp [EV]
  have e2 : (a.tw s).ρ (frob h) = (qPow w s : ℂ) • a.ρ (frob h) := by simp [deg_frob]
  rw [e2] at hr
  have := ha χ (fun u hu => h0 u ((e u).2 hu)) _ v ((e v).1 hv) (absSpace_smul (qPow w s).ne_zero hr) hv0
  rwa [norm_qPow] at this

/- English proof (translation)
Take `⟨m, hm, hc⟩` from `GlobalTheory.IrrWeilAbs.exists_pow_central a (deg_frob (h := h))`. Rewrite `hv`, the goal using `[← GlobalTheory.CompanionTheory.TempRes.absSpace_pow_eq (a.semisimple _) hr hm.ne', ← map_pow]`. Conclude with `map_absSpace_le (a.ρ σ) (fun u => (LinearMap.congr_fun (hc σ) u).symm) _ ⟨v, hv, rfl⟩`.
-/
theorem abs_stable {n : ℕ} (a : WDRep h (Fin n → ℂ)) (σ : Weil h) {r : ℝ} (hr : 0 ≤ r) {v : Fin n → ℂ}
    (hv : v ∈ absSpace (a.ρ (frob h)) r) : a.ρ σ v ∈ absSpace (a.ρ (frob h)) r := by
  obtain ⟨m, hm, hc⟩ := GlobalTheory.IrrWeilAbs.exists_pow_central a (deg_frob (h := h))
  rw [← GlobalTheory.CompanionTheory.TempRes.absSpace_pow_eq (a.semisimple _) hr hm.ne', ← map_pow] at hv ⊢
  exact map_absSpace_le (a.ρ σ) (fun u => (LinearMap.congr_fun (hc σ) u).symm) _ ⟨v, hv, rfl⟩

/- English proof (translation)
Introduce `χ h0 r v hv hr hv0`. Establish `hp` using `ht (frob h) deg_frob`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Choose the witnesses or unpack the hypotheses as in `⟨i, rfl⟩ : ∃ i : ℤ, r = ((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2) := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `hd` using `(End.eigenspaces_iSupIndep (a.ρ (frob h))).disjoint_biSup_biSup (s := {α | ‖α‖ = r}) (t := {α | ‖α‖ = r}ᶜ) disjoint_compl_right`. Establish `hle : (⨆ i : ℤ, absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2))) ≤ ⨆ β ∈ ({α | ‖α‖ = r}ᶜ : Set ℂ), End.eigenspace (a.ρ (frob h)) β` using `iSup_le fun i => iSup₂_le fun β hβ => le_iSup₂_of_le β (fun k => hc i (k.symm.trans hβ)) le_rfl`. Rewrite `hle` using `[hp.1]`. Conclude with `hv0 (Submodule.disjoint_def.1 hd v hr (hle Submodule.mem_top))`.

Establish `kill : ∀ (k : ℕ) u, EV a χ u → (a.N ^ (k + 1)) u = 0` using `fun k u hu => by`. Rewrite using `[pow_succ, End.mul_apply, h0 u hu, map_zero]`. Establish `comm : ∀ (k : ℕ) (s : ↥(Ine (F` using `E) A)) u, a.ρ (ineIncl h s) ((a.N ^ k) u) = (a.N ^ k) (a.ρ (ineIncl h s) u) := by`. Introduce `k s`. Proceed by induction on `k with`.

Consider the case `zero => intro u`. Simplify using the standard rewrite rules. Consider the case `succ k ih => intro u`. Rewrite using `[pow_succ', End.mul_apply, End.mul_apply, a.comm_apply, ih]`. Simplify using the standard rewrite rules.

Break down `i with (_ | k) | k` into its components or cases. Simplify using the standard rewrite rules. It suffices to derive a contradiction. Take `⟨u, hu, e⟩` from `(hp.2 (k + 1)).surjOn (show v ∈ _ from by simpa using hr)`. Establish `hE : EV a χ u` using `fun s => by`.

Use `(hp.2 (k + 1)).injOn (abs_stable a _ (Real.rpow_nonneg (by positivity) _) hu) (Submodule.smul_mem _ _ hu) ?_` and prove the remaining obligations. Use `show (a.N ^ (k + 1)) _ = (a.N ^ (k + 1)) _`. Rewrite using `[← comm, map_smul, e, hv s]`. Conclude with `hv0 (e.symm.trans (kill k u hE))`. It suffices to derive a contradiction.

Use `hv0 ((hp.2 (k + 1)).injOn (show v ∈ _ from ?_) (Submodule.zero_mem _) ?_)` and prove the remaining obligations. Establish `e : ((Int.negSucc k : ℤ) : ℝ) / 2 = -((k + 1 : ℕ) : ℝ) / 2` using `by rw [Int.cast_negSucc]`. Rewrite `hr` using `[e]`. Then use the resulting hypothesis. Use `show (a.N ^ (k + 1)) _ = (a.N ^ (k + 1)) _`. Rewrite using `[kill k v hv, map_zero]`.
-/
theorem win_of_tempered {n : ℕ} {a : WDRep h (Fin n → ℂ)} (ht : a.Tempered) : Win a {1} := by
  intro χ h0 r v hv hr hv0
  have hp := ht (frob h) deg_frob
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, r = ((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2) := by
    by_contra hc
    push Not at hc
    have hd := (End.eigenspaces_iSupIndep (a.ρ (frob h))).disjoint_biSup_biSup (s := {α | ‖α‖ = r}) (t := {α | ‖α‖ = r}ᶜ)
      disjoint_compl_right
    have hle : (⨆ i : ℤ, absSpace (a.ρ (frob h)) (((normV w : ℕ) : ℝ) ^ ((i : ℝ) / 2))) ≤
        ⨆ β ∈ ({α | ‖α‖ = r}ᶜ : Set ℂ), End.eigenspace (a.ρ (frob h)) β :=
      iSup_le fun i => iSup₂_le fun β hβ => le_iSup₂_of_le β (fun k => hc i (k.symm.trans hβ)) le_rfl
    rw [hp.1] at hle
    exact hv0 (Submodule.disjoint_def.1 hd v hr (hle Submodule.mem_top))
  have kill : ∀ (k : ℕ) u, EV a χ u → (a.N ^ (k + 1)) u = 0 := fun k u hu => by
    rw [pow_succ, End.mul_apply, h0 u hu, map_zero]
  have comm : ∀ (k : ℕ) (s : ↥(Ine (F := E) A)) u, a.ρ (ineIncl h s) ((a.N ^ k) u) = (a.N ^ k) (a.ρ (ineIncl h s) u) := by
    intro k s
    induction k with
    | zero => intro u; simp
    | succ k ih => intro u; rw [pow_succ', End.mul_apply, End.mul_apply, a.comm_apply, ih]; simp
  rcases i with (_ | k) | k
  · simp
  · exfalso
    obtain ⟨u, hu, e⟩ := (hp.2 (k + 1)).surjOn (show v ∈ _ from by simpa using hr)
    have hE : EV a χ u := fun s => by
      refine (hp.2 (k + 1)).injOn (abs_stable a _ (Real.rpow_nonneg (by positivity) _) hu) (Submodule.smul_mem _ _ hu) ?_
      show (a.N ^ (k + 1)) _ = (a.N ^ (k + 1)) _
      rw [← comm, map_smul, e, hv s]
    exact hv0 (e.symm.trans (kill k u hE))
  · exfalso
    refine hv0 ((hp.2 (k + 1)).injOn (show v ∈ _ from ?_) (Submodule.zero_mem _) ?_)
    · have e : ((Int.negSucc k : ℤ) : ℝ) / 2 = -((k + 1 : ℕ) : ℝ) / 2 := by rw [Int.cast_negSucc]
      rwa [e] at hr
    · show (a.N ^ (k + 1)) _ = (a.N ^ (k + 1)) _
      rw [kill k v hv, map_zero]

/- English proof (translation)
Take `⟨m, hm, hc⟩` from `GlobalTheory.IrrWeilAbs.exists_pow_central x (deg_frob (h := h))`. Set `U : Submodule ℂ (Fin n → ℂ)` to `{ carrier := {u | EV x χ u} add_mem' := fun {p q} hp hq s => by rw [map_add, hp s, hq s, smul_add] zero_mem' := fun s => by simp smul_mem' := fun c p hp s => by rw [map_smul, hp s, smul_comm] }`. Set `ψ` to `x.ρ (frob h ^ m)`. Establish `hU : ∀ u ∈ U, ψ u ∈ U` using `fun u hu s => by`. Use `LinearMap.congr_fun (hc (ineIncl h s)) u` as an intermediate fact.

Simplify using `only [End.mul_apply] at this`. Rewrite using `[← this, hu s, map_smul]`. Establish `hs : End.IsSemisimple (ψ.restrict hU)` using `(x.semisimple _).restrict hU`. Establish `htop` using `GlobalTheory.CompanionTheory.TempRes.iSup_eigenspace_eq_top hs`. Establish `hle : (⨆ μ, End.eigenspace (ψ.restrict hU) μ) ≤ LinearMap.ker (x.N ∘ₗ U.subtype)` using `iSup_le fun μ u hu => by`.

Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply]`. Assume the negation of the conclusion as `hN`. Establish `hu0 : (u : Fin n → ℂ) ≠ 0` using `fun e => hN (by rw [Submodule.subtype_apply, e, map_zero])`. Establish `h1 : ψ u = μ • (u : Fin n → ℂ)` using `congrArg Subtype.val (End.mem_eigenspace_iff.1 hu)`. Establish `hr : 0 ≤ ‖μ‖ ^ ((m : ℝ)⁻¹)` using `Real.rpow_nonneg (norm_nonneg _) _`.

Establish `h2 : (u : Fin n → ℂ) ∈ absSpace (x.ρ (frob h)) (‖μ‖ ^ ((m : ℝ)⁻¹))`. Rewrite using `[← GlobalTheory.CompanionTheory.TempRes.absSpace_pow_eq (x.semisimple _) hr hm.ne', ← map_pow, Real.rpow_inv_natCast_pow (norm_nonneg _) hm.ne']`. Conclude with `Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem rfl (End.mem_eigenspace_iff.2 h1))`. Establish `h3` using `absSpace_shift (x.comm_apply (frob h)) h2`. Rewrite `h3` using `[deg_frob, zpow_one, Complex.norm_natCast]`.

Use `hS _ (hw _ _ u.2 h2 hu0) (hw _ _ (fun s => ?_) h3 hN)` and prove the remaining obligations. Rewrite using `[x.comm_apply, u.2 s, map_smul]`. Simplify using the standard rewrite rules. Rewrite `hle` using `[htop]`. Conclude with `hle (x := ⟨v, hv⟩) Submodule.mem_top`.
-/
theorem kill_of_win {n : ℕ} (x : WDRep h (Fin n → ℂ)) (χ : ↥(Ine (F := E) A) → ℂ) (S : Set ℝ)
    (hS : ∀ r ∈ S, ((normV w : ℕ) : ℝ) * r ∉ S)
    (hw : ∀ r v, EV x χ v → v ∈ absSpace (x.ρ (frob h)) r → v ≠ 0 → r ∈ S) (v : Fin n → ℂ) (hv : EV x χ v) : x.N v = 0 := by
  obtain ⟨m, hm, hc⟩ := GlobalTheory.IrrWeilAbs.exists_pow_central x (deg_frob (h := h))
  let U : Submodule ℂ (Fin n → ℂ) :=
    { carrier := {u | EV x χ u}
      add_mem' := fun {p q} hp hq s => by rw [map_add, hp s, hq s, smul_add]
      zero_mem' := fun s => by simp
      smul_mem' := fun c p hp s => by rw [map_smul, hp s, smul_comm] }
  let ψ := x.ρ (frob h ^ m)
  have hU : ∀ u ∈ U, ψ u ∈ U := fun u hu s => by
    have := LinearMap.congr_fun (hc (ineIncl h s)) u
    simp only [End.mul_apply] at this
    rw [← this, hu s, map_smul]
  have hs : End.IsSemisimple (ψ.restrict hU) := (x.semisimple _).restrict hU
  have htop := GlobalTheory.CompanionTheory.TempRes.iSup_eigenspace_eq_top hs
  have hle : (⨆ μ, End.eigenspace (ψ.restrict hU) μ) ≤ LinearMap.ker (x.N ∘ₗ U.subtype) := iSup_le fun μ u hu => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    by_contra hN
    have hu0 : (u : Fin n → ℂ) ≠ 0 := fun e => hN (by rw [Submodule.subtype_apply, e, map_zero])
    have h1 : ψ u = μ • (u : Fin n → ℂ) := congrArg Subtype.val (End.mem_eigenspace_iff.1 hu)
    have hr : 0 ≤ ‖μ‖ ^ ((m : ℝ)⁻¹) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (u : Fin n → ℂ) ∈ absSpace (x.ρ (frob h)) (‖μ‖ ^ ((m : ℝ)⁻¹)) := by
      rw [← GlobalTheory.CompanionTheory.TempRes.absSpace_pow_eq (x.semisimple _) hr hm.ne', ← map_pow,
        Real.rpow_inv_natCast_pow (norm_nonneg _) hm.ne']
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem rfl (End.mem_eigenspace_iff.2 h1))
    have h3 := absSpace_shift (x.comm_apply (frob h)) h2
    rw [deg_frob, zpow_one, Complex.norm_natCast] at h3
    refine hS _ (hw _ _ u.2 h2 hu0) (hw _ _ (fun s => ?_) h3 hN)
    rw [x.comm_apply, u.2 s, map_smul]
    simp
  rw [htop] at hle
  exact hle (x := ⟨v, hv⟩) Submodule.mem_top

def Shape (y : WD h) : Prop :=
  ∃ L : List (WD h), (∀ z ∈ L, ∃ (t : WD h) (s : ℝ), t.tempered ∧ |s| < 1 / 2 ∧ z = t.lpTw s) ∧ y = sumList L

def window (w : HeightOneSpectrum (𝓞 E)) : Set ℝ :=
  Set.Ioo (((normV w : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) (((normV w : ℕ) : ℝ) ^ (1 / 2 : ℝ))

/- English proof (translation)
Take `⟨L, hL, rfl⟩` from `hy`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `key : ∀ L : List (WD h), (∀ z ∈ L, ∃ (t : WD h) (s : ℝ), t.tempered ∧ |s| < 1 / 2 ∧ z = t.lpTw s) → ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)), WD.mk b = sumList L ∧ Win b (window w)`. Introduce `L`. Proceed by induction on `L with`.

Consider the case `nil => exact fun _ => ⟨0, _, rfl, fun χ _ r v _ _ hv => absurd (Subsingleton.elim _ _) hv⟩`. Consider the case `cons z L ih`. Introduce `hL`. Take `⟨n, b, eb, hb⟩` from `ih fun z hz => hL z (List.mem_cons_of_mem _ hz)`. Take `⟨t, s, ht, hs, rfl⟩` from `hL z List.mem_cons_self`.

Take `⟨k, t, rfl⟩` from `t.exists_rep`. Take `⟨j, c, ec⟩` from `(sumList ((WD.mk t).lpTw s :: L)).exists_rep`. Use `⟨j, c, ec, Win.iso (b := (t.tw s).sum b) (WD.mk_eq_mk.1 ?_) (Win.sum ?_ hb)⟩` and prove the remaining obligations. Rewrite using `[ec, ← WD.lpSum_mk, eb, ← WD.lpTw_mk]`. Both sides reduce to the same expression.

Use `((win_of_tempered ((WD.tempered_mk _).1 ht)).tw s).mono fun r hr => ?_` and prove the remaining obligations. Establish `h1 : r = ((normV w : ℕ) : ℝ) ^ s`. Establish `: r / ((normV w : ℕ) : ℝ) ^ s = 1` using `hr`. Conclude with `(div_eq_one_iff_eq (Real.rpow_pos_of_pos (by linarith) s).ne').1 this`. Rewrite using `[h1]`.

Conclude with `⟨Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).1, Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).2⟩`. Take `⟨n, b, eb, hb⟩` from `key L hL`. Conclude with `Win.iso (WD.mk_eq_mk.1 (e.trans eb.symm)) hb`.
-/
theorem Shape.win {y : WD h} (hy : Shape y) {a : WDRep h V} (e : WD.mk a = y) : Win a (window w) := by
  obtain ⟨L, hL, rfl⟩ := hy
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have key : ∀ L : List (WD h), (∀ z ∈ L, ∃ (t : WD h) (s : ℝ), t.tempered ∧ |s| < 1 / 2 ∧ z = t.lpTw s) →
      ∃ (n : ℕ) (b : WDRep h (Fin n → ℂ)), WD.mk b = sumList L ∧ Win b (window w) := by
    intro L
    induction L with
    | nil => exact fun _ => ⟨0, _, rfl, fun χ _ r v _ _ hv => absurd (Subsingleton.elim _ _) hv⟩
    | cons z L ih =>
      intro hL
      obtain ⟨n, b, eb, hb⟩ := ih fun z hz => hL z (List.mem_cons_of_mem _ hz)
      obtain ⟨t, s, ht, hs, rfl⟩ := hL z List.mem_cons_self
      obtain ⟨k, t, rfl⟩ := t.exists_rep
      obtain ⟨j, c, ec⟩ := (sumList ((WD.mk t).lpTw s :: L)).exists_rep
      refine ⟨j, c, ec, Win.iso (b := (t.tw s).sum b) (WD.mk_eq_mk.1 ?_) (Win.sum ?_ hb)⟩
      · rw [ec, ← WD.lpSum_mk, eb, ← WD.lpTw_mk]
        rfl
      · refine ((win_of_tempered ((WD.tempered_mk _).1 ht)).tw s).mono fun r hr => ?_
        have h1 : r = ((normV w : ℕ) : ℝ) ^ s := by
          have : r / ((normV w : ℕ) : ℝ) ^ s = 1 := hr
          exact (div_eq_one_iff_eq (Real.rpow_pos_of_pos (by linarith) s).ne').1 this
        rw [h1]
        exact ⟨Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).1, Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).2⟩
  obtain ⟨n, b, eb, hb⟩ := key L hL
  exact Win.iso (WD.mk_eq_mk.1 (e.trans eb.symm)) hb

/- English proof (translation)
Rewrite using `[WD.eig, WD.eig, WD.eig, WD.charPol_lpSum]`. Conclude with `Polynomial.roots_mul ((WD.charPol_monic x g).mul (WD.charPol_monic _ g)).ne_zero`.
-/
theorem eig_sum (x y : WD h) (g : Weil h) : (x.lpSum y).eig g = x.eig g + y.eig g := by
  rw [WD.eig, WD.eig, WD.eig, WD.charPol_lpSum]
  exact Polynomial.roots_mul ((WD.charPol_monic x g).mul (WD.charPol_monic _ g)).ne_zero

/- English proof (translation)
Take `⟨L, hL, rfl⟩` from `hy`. Proceed by induction on `L with`. Consider the case `nil`. Use `WD.card_eig (WD.lpZero h) φ` as an intermediate fact. Rewrite `this` using `[WD.lpDim_zero, Multiset.card_eq_zero]`.

Conclude with `absurd (this ▸ hα : α ∈ (0 : Multiset ℂ)) (Multiset.notMem_zero _)`. Consider the case `cons z L ih`. Express the relevant statement in the definitionally equal form `α ∈ (z.lpSum (sumList L)).eig φ at hα`. Express the relevant statement in the definitionally equal form `∃ (t : WD h) (s : ℝ) (β : ℂ), _ ∧ _ ∧ _ ≤ (z.lpSum (sumList L)).lpDim ∧ ((z.lpSum (sumList L)).mono0 → _) ∧ _`. Rewrite `hα` using `[eig_sum, Multiset.mem_add]`.

Rewrite using `[WD.lpDim_sum, WD.monomial_sum_iff]`. Break down `hα with hα | hα` into its components or cases. Take `⟨t, s, ht, hs, rfl⟩` from `hL z List.mem_cons_self`. Rewrite `hα` using `[GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ]`. Take `⟨β, hβ, rfl⟩` from `Multiset.mem_map.1 hα`.

Conclude with `⟨t, s, β, ht, hs, by rw [WD.lpDim_tw]; omega, fun m => (WD.monomial_twist_iff _ _).1 m.1, hβ, by rw [norm_mul, ← coe_qPow, norm_qPow]⟩`. Take `⟨t, s, β, ht, hs, hd, hm, k⟩` from `ih (fun z hz => hL z (List.mem_cons_of_mem _ hz)) hα`. Conclude with `⟨t, s, β, ht, hs, by omega, fun m => hm m.2, k⟩`.
-/
theorem Shape.eig {y : WD h} (hy : Shape y) {φ : Weil h} (hφ : deg φ = 1) {α : ℂ} (hα : α ∈ y.eig φ) :
    ∃ (t : WD h) (s : ℝ) (β : ℂ), t.tempered ∧ |s| < 1 / 2 ∧ t.lpDim ≤ y.lpDim ∧ (y.mono0 → t.mono0) ∧ β ∈ t.eig φ ∧
      ‖α‖ = ‖β‖ * ((normV w : ℕ) : ℝ) ^ s := by
  obtain ⟨L, hL, rfl⟩ := hy
  induction L with
  | nil =>
    have := WD.card_eig (WD.lpZero h) φ
    rw [WD.lpDim_zero, Multiset.card_eq_zero] at this
    exact absurd (this ▸ hα : α ∈ (0 : Multiset ℂ)) (Multiset.notMem_zero _)
  | cons z L ih =>
    change α ∈ (z.lpSum (sumList L)).eig φ at hα
    change ∃ (t : WD h) (s : ℝ) (β : ℂ), _ ∧ _ ∧ _ ≤ (z.lpSum (sumList L)).lpDim ∧ ((z.lpSum (sumList L)).mono0 → _) ∧ _
    rw [eig_sum, Multiset.mem_add] at hα
    rw [WD.lpDim_sum, WD.monomial_sum_iff]
    rcases hα with hα | hα
    · obtain ⟨t, s, ht, hs, rfl⟩ := hL z List.mem_cons_self
      rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ] at hα
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hα
      exact ⟨t, s, β, ht, hs, by rw [WD.lpDim_tw]; omega, fun m => (WD.monomial_twist_iff _ _).1 m.1, hβ,
        by rw [norm_mul, ← coe_qPow, norm_qPow]⟩
    · obtain ⟨t, s, β, ht, hs, hd, hm, k⟩ := ih (fun z hz => hL z (List.mem_cons_of_mem _ hz)) hα
      exact ⟨t, s, β, ht, hs, by omega, fun m => hm m.2, k⟩

/- English proof (translation)
Proceed by induction on `t using WD.ind with`. Consider the case `hP n b`. Rewrite `hβ` using `[WD.eig, WD.charPol_mk]`. Rewrite `ht` using `[WD.tempered_mk]`. Rewrite using `[WD.lpDim_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff]`.

Establish `hev : End.HasEigenvalue (b.ρ φ) β` using `(End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr ((mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hβ)`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `k` using `GlobalTheory.LocalInv.norm_le_of_isPurePair hq b.nilpotent (ht φ hφ) hev`. Use `⟨k.1, k.2, fun m => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hev.exists_hasEigenvector`.

Conclude with `absSpace_disj (Submodule.mem_iSup_of_mem β (Submodule.mem_iSup_of_mem rfl hv.1)) (by rw [ht.norm_eq_one m hφ]; trivial) hv.2`.
-/
theorem norm_le_of_tempered {t : WD h} (ht : t.tempered) {φ : Weil h} (hφ : deg φ = 1) {β : ℂ} (hβ : β ∈ t.eig φ) :
    ((normV w : ℕ) : ℝ) ^ (-(((t.lpDim : ℝ) - 1) / 2)) ≤ ‖β‖ ∧ ‖β‖ ≤ ((normV w : ℕ) : ℝ) ^ (((t.lpDim : ℝ) - 1) / 2) ∧
      (t.mono0 → ‖β‖ = 1) := by
  induction t using WD.ind with
  | hP n b =>
    rw [WD.eig, WD.charPol_mk] at hβ
    rw [WD.tempered_mk] at ht
    rw [WD.lpDim_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    have hev : End.HasEigenvalue (b.ρ φ) β :=
      (End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr ((mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hβ)
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    have k := GlobalTheory.LocalInv.norm_le_of_isPurePair hq b.nilpotent (ht φ hφ) hev
    refine ⟨k.1, k.2, fun m => ?_⟩
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    exact absSpace_disj (Submodule.mem_iSup_of_mem β (Submodule.mem_iSup_of_mem rfl hv.1))
      (by rw [ht.norm_eq_one m hφ]; trivial) hv.2

/- English proof (translation)
Take `⟨t, s, β, ht, hs, hd, -, hβ, e⟩` from `hy.eig hφ hα`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Establish `hd' : (t.lpDim : ℝ) ≤ y.lpDim` using `by exact_mod_cast hd`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.rpow_add (by linarith)]`. Conclude with `Real.rpow_lt_rpow_of_exponent_lt hq (by linarith [(abs_lt.1 hs).2])`.
-/
theorem Shape.norm_lt {y : WD h} (hy : Shape y) {φ : Weil h} (hφ : deg φ = 1) {α : ℂ} (hα : α ∈ y.eig φ) :
    ‖α‖ < ((normV w : ℕ) : ℝ) ^ ((y.lpDim : ℝ) / 2) := by
  obtain ⟨t, s, β, ht, hs, hd, -, hβ, e⟩ := hy.eig hφ hα
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hd' : (t.lpDim : ℝ) ≤ y.lpDim := by exact_mod_cast hd
  rw [e]
  calc _ ≤ ((normV w : ℕ) : ℝ) ^ (((t.lpDim : ℝ) - 1) / 2) * ((normV w : ℕ) : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (norm_le_of_tempered ht hφ hβ).2.1 (Real.rpow_nonneg (by linarith) _)
    _ < _ := by
        rw [← Real.rpow_add (by linarith)]
        exact Real.rpow_lt_rpow_of_exponent_lt hq (by linarith [(abs_lt.1 hs).2])

/- English proof (translation)
Introduce `φ hφ α hα` and use `(hy.norm_lt hφ hα).le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (one_lt_normV w).le) (by linarith))`.
-/
theorem Shape.sz {y : WD h} (hy : Shape y) : Sz y := fun φ hφ α hα =>
  (hy.norm_lt hφ hα).le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (one_lt_normV w).le) (by linarith))

/- English proof (translation)
Take `⟨t, s, β, ht, hs, -, hm', hβ, e⟩` from `hy.eig hφ hα`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast one_lt_normV w`. Rewrite using `[e, (norm_le_of_tempered ht hφ hβ).2.2 (hm' hm), one_mul]`. Conclude with `⟨Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).1, Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).2⟩`.
-/
theorem Shape.mem_window {y : WD h} (hy : Shape y) (hm : y.mono0) {φ : Weil h} (hφ : deg φ = 1) {α : ℂ}
    (hα : α ∈ y.eig φ) : ‖α‖ ∈ window w := by
  obtain ⟨t, s, β, ht, hs, -, hm', hβ, e⟩ := hy.eig hφ hα
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  rw [e, (norm_le_of_tempered ht hφ hβ).2.2 (hm' hm), one_mul]
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).1, Real.rpow_lt_rpow_of_exponent_lt hq (abs_lt.1 hs).2⟩

/- English proof (translation)
Establish `hq : (0 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast zero_lt_one.trans (one_lt_normV w)`. Use `ha.2.trans_le ?_` and prove the remaining obligations. Establish `e : ((normV w : ℕ) : ℝ) ^ (1 / 2 : ℝ) = ((normV w : ℕ) : ℝ) * ((normV w : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)`. Rewrite using `[show (1 / 2 : ℝ) = 1 + -(1 / 2) by norm_num, Real.rpow_add hq, Real.rpow_one]; norm_num`. Rewrite using `[e]`.

Conclude with `mul_le_mul_of_nonneg_left hb.1.le hq.le`.
-/
theorem window_ratio {a b : ℝ} (ha : a ∈ window w) (hb : b ∈ window w) : a < ((normV w : ℕ) : ℝ) * b := by
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast zero_lt_one.trans (one_lt_normV w)
  refine ha.2.trans_le ?_
  have e : ((normV w : ℕ) : ℝ) ^ (1 / 2 : ℝ) = ((normV w : ℕ) : ℝ) * ((normV w : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + -(1 / 2) by norm_num, Real.rpow_add hq, Real.rpow_one]; norm_num
  rw [e]
  exact mul_le_mul_of_nonneg_left hb.1.le hq.le

/- English proof (translation)
Establish `k : ∀ γ ∈ y.eig φ, ‖γ‖ * ((normV w : ℕ) : ℝ) ^ c ∈ window w` using `fun γ hγ => by`. Rewrite using `[← norm_qPow, ← norm_mul]`. Use `hy.mem_window ((WD.monomial_twist_iff _ _).2 hm) hφ ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ]`. Conclude with `Multiset.mem_map_of_mem _ hγ`.

Establish `hq : (0 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast zero_lt_one.trans (one_lt_normV w)`. Use `window_ratio (k α hα) (k β hβ)` as an intermediate fact. Rewrite `this` using `[← mul_assoc]`. Conclude with `lt_of_mul_lt_mul_right this (Real.rpow_nonneg hq.le _)`.
-/
theorem Shape.ratio {y : WD h} {c : ℝ} (hy : Shape (y.lpTw c)) (hm : y.mono0) {φ : Weil h} (hφ : deg φ = 1)
    {α β : ℂ} (hα : α ∈ y.eig φ) (hβ : β ∈ y.eig φ) : ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖ := by
  have k : ∀ γ ∈ y.eig φ, ‖γ‖ * ((normV w : ℕ) : ℝ) ^ c ∈ window w := fun γ hγ => by
    rw [← norm_qPow, ← norm_mul]
    refine hy.mem_window ((WD.monomial_twist_iff _ _).2 hm) hφ ?_
    rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ]
    exact Multiset.mem_map_of_mem _ hγ
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast zero_lt_one.trans (one_lt_normV w)
  have := window_ratio (k α hα) (k β hβ)
  rw [← mul_assoc] at this
  exact lt_of_mul_lt_mul_right this (Real.rpow_nonneg hq.le _)

/- English proof (translation)
Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Rewrite using `[WD.monodromyZero_ofWeilDeligneRepClass_iff]`. Establish `hm : ∀ {β : ℂ} {v : Fin n → ℂ}, v ≠ 0 → a.ρ (frob h) v = β • v → β ∈ (WD.mk a).eig (frob h)` using `fun hv e => by`. Rewrite using `[WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly]`.

Conclude with `End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.2 e, hv⟩`. Use `LinearMap.ker_eq_top.1 (top_le_iff.1 ?_)` and prove the remaining obligations. Rewrite using `[← (a.semisimple (frob h)).iSup_eigenspace_eq_top]`. Use `iSup_le fun β v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Establish `hv0 : v ≠ 0` using `by rintro rfl; exact h0 (map_zero _)`. Establish `e` using `End.mem_eigenspace_iff.1 hv`. Use `hx (((normV w : ℕ) : ℂ) * β) (hm h0 (by rw [a.comm_apply, e, map_smul, smul_smul, deg_frob, zpow_one])) β (hm hv0 e)` as an intermediate fact. Rewrite `this` using `[norm_mul, Complex.norm_natCast]`. Conclude with `lt_irrefl _ this`.
-/
theorem monodromy_free_of_eigenvalue_ratio {x : WD h}
    (hx : ∀ α ∈ x.eig (frob h), ∀ β ∈ x.eig (frob h), ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖) : x.mono0 := by
  induction x using WD.ind with
  | hP n a =>
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
    have hm : ∀ {β : ℂ} {v : Fin n → ℂ}, v ≠ 0 → a.ρ (frob h) v = β • v → β ∈ (WD.mk a).eig (frob h) := fun hv e => by
      rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly]
      exact End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.2 e, hv⟩
    refine LinearMap.ker_eq_top.1 (top_le_iff.1 ?_)
    rw [← (a.semisimple (frob h)).iSup_eigenspace_eq_top]
    refine iSup_le fun β v hv => ?_
    by_contra h0
    have hv0 : v ≠ 0 := by rintro rfl; exact h0 (map_zero _)
    have e := End.mem_eigenspace_iff.1 hv
    have := hx (((normV w : ℕ) : ℂ) * β) (hm h0 (by rw [a.comm_apply, e, map_smul, smul_smul, deg_frob, zpow_one])) β (hm hv0 e)
    rw [norm_mul, Complex.norm_natCast] at this
    exact lt_irrefl _ this

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `x.exists_rep`. Take `⟨m, b, rfl⟩` from `y.exists_rep`. Rewrite `hx`, `hy` using `[WD.monodromyZero_ofWeilDeligneRepClass_iff]`. Take `⟨e, he⟩` from `GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n m a b fun σ => by simpa using hc σ`. Conclude with `WD.sound ⟨e, he, fun v => by rw [show a.N = 0 from hx, show b.N = 0 from hy]; simp⟩`.
-/
theorem eq_of_mono0 {x y : WD h} (hc : ∀ g, x.charPol g = y.charPol g) (hx : x.mono0) (hy : y.mono0) : x = y := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  obtain ⟨m, b, rfl⟩ := y.exists_rep
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hx hy
  obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n m a b fun σ => by simpa using hc σ
  exact WD.sound ⟨e, he, fun v => by rw [show a.N = 0 from hx, show b.N = 0 from hy]; simp⟩

/- English proof (translation)
Use `aw_of_eigen hp (fun m => eq_of_mono0 hp (monodromy_free_of_eigenvalue_ratio fun α hα β hβ => ?_) m) ?_` and prove the remaining obligations. Rewrite `hα`, `hβ` using `[WD.eig, hp]`. Conclude with `hy.ratio m deg_frob hα hβ`. Introduce and unpack `n a b rfl rfl χ h0 v hv`. Take `⟨e, he⟩` from `GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n a b fun σ => by simpa using hp σ`.

Establish `hw` using `((hy.win (a := b.tw c) (WD.lpTw_mk b c).symm).tw (-c))`. Establish `hq : (0 : ℝ) < ((normV w : ℕ) : ℝ)` using `by exact_mod_cast zero_lt_one.trans (one_lt_normV w)`. Establish `hb : Win b {r | r / ((normV w : ℕ) : ℝ) ^ (-c) ∈ window w}`. Use `Win.iso (WD.mk_eq_mk.1 ?_) hw` and prove the remaining obligations. Rewrite using `[← WD.lpTw_mk, ← WD.lpTw_mk, WD.lpTw_add, add_neg_cancel, WD.lpTw_zero]`.

Use `kill_of_win a χ _ (fun r hr hr' => ?_) (fun r u hu hr hu0 => hb χ h0 r (e u) (fun s => by rw [← he, hu s, map_smul]) (map_absSpace_le e.toLinearMap (fun z => he _ z) r ⟨u, hr, rfl⟩) (e.map_ne_zero_iff.2 hu0)) v hv` and prove the remaining obligations. Use `window_ratio hr' hr` as an intermediate fact. Rewrite `this` using `[mul_div_assoc]`. Conclude with `lt_irrefl _ this`.
-/
theorem aw_of_shape {x y : WD h} {c : ℝ} (hp : ∀ g : Weil h, x.charPol g = y.charPol g) (hy : Shape (y.lpTw c)) : Aw x y := by
  refine aw_of_eigen hp (fun m => eq_of_mono0 hp (monodromy_free_of_eigenvalue_ratio fun α hα β hβ => ?_) m) ?_
  · rw [WD.eig, hp] at hα hβ
    exact hy.ratio m deg_frob hα hβ
  · rintro n a b rfl rfl χ h0 v hv
    obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n a b fun σ => by simpa using hp σ
    have hw := ((hy.win (a := b.tw c) (WD.lpTw_mk b c).symm).tw (-c))
    have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast zero_lt_one.trans (one_lt_normV w)
    have hb : Win b {r | r / ((normV w : ℕ) : ℝ) ^ (-c) ∈ window w} := by
      refine Win.iso (WD.mk_eq_mk.1 ?_) hw
      rw [← WD.lpTw_mk, ← WD.lpTw_mk, WD.lpTw_add, add_neg_cancel, WD.lpTw_zero]
    refine kill_of_win a χ _ (fun r hr hr' => ?_) (fun r u hu hr hu0 => hb χ h0 r (e u)
      (fun s => by rw [← he, hu s, map_smul]) (map_absSpace_le e.toLinearMap (fun z => he _ z) r ⟨u, hr, rfl⟩)
      (e.map_ne_zero_iff.2 hu0)) v hv
    have := window_ratio hr' hr
    rw [mul_div_assoc] at this
    exact lt_irrefl _ this

end UpperTheory.GalN
