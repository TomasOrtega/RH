import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepA

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

def PosInt (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  IsInvIntegral I ∧ (∀ f, IsTestFun f → I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f)) ∧
    ∀ f, IsTestFun f → (∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0)

/- English proof (translation)
Establish `h` using `isTestFun_mul y (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g)) (fun u hu g => by show (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) (u * g)) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g)`. Rewrite using `[WT.left x hu, map_mul, conj_psi]) (x.2.2.1.comp _)`. Establish `e : (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g) = fun g => (y : GL (Fin m) k → ℂ) g * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g)`. Use function extensionality and compare the values at `fun g => mul_comm _ _`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem isTestFun_pair (x y : WT (m := m) ψ) :
    IsTestFun fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g := by
  have h := isTestFun_mul y (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g))
    (fun u hu g => by
      show (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) (u * g)) =
        ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g)
      rw [WT.left x hu, map_mul, conj_psi]) (x.2.2.1.comp _)
  have e : (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g) =
      fun g => (y : GL (Fin m) k → ℂ) g * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) :=
    funext fun g => mul_comm _ _
  rw [e]
  exact h

/- English proof (translation)
Use `⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩` and prove the remaining obligations. Rewrite using `[formI_apply, formI_apply, ← hI.2.1 _ (isTestFun_pair x y)]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [map_mul, Complex.conj_conj]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(hI.2.2 _ (isTestFun_pair x x) fun g => by rw [conj_mul_self_re]; exact Complex.normSq_nonneg _).1`. Rewrite using `[formI_apply, formI_apply]`. Simplify using `only [rhoW_apply]`. Conclude with `hI.1 _ (isTestFun_pair x y) g`.
-/
theorem isInvForm_formI {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) :
    IsInvForm (rhoW ψ) (formI ψ I) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩
  · rw [formI_apply, formI_apply, ← hI.2.1 _ (isTestFun_pair x y)]
    congr 1
    funext g
    simp only [map_mul, Complex.conj_conj]
    ring
  · exact (hI.2.2 _ (isTestFun_pair x x) fun g => by rw [conj_mul_self_re]; exact Complex.normSq_nonneg _).1
  · rw [formI_apply, formI_apply]
    simp only [rhoW_apply]
    exact hI.1 _ (isTestFun_pair x y) g

/- English proof (translation)
Introduce `h0`. Apply `hx` to reduce the goal to its premises. Establish `hn : ∀ g, 0 ≤ ((starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (x : GL (Fin m) k → ℂ) g).re` using `fun g => by`. Rewrite using `[conj_mul_self_re]`. Conclude with `Complex.normSq_nonneg _`.

Establish `h` using `(hI.2.2 _ (isTestFun_pair x x) hn).2 (by rw [← formI_apply, h0, Complex.zero_re])`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Use `h g` as an intermediate fact. Rewrite `this` using `[conj_mul_self_re]`. Conclude with `Complex.normSq_eq_zero.1 this`.
-/
theorem formI_self_ne_zero {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) {x : WT (m := m) ψ} (hx : x ≠ 0) :
    formI ψ I x x ≠ 0 := by
  intro h0
  apply hx
  have hn : ∀ g, 0 ≤ ((starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (x : GL (Fin m) k → ℂ) g).re := fun g => by
    rw [conj_mul_self_re]; exact Complex.normSq_nonneg _
  have h := (hI.2.2 _ (isTestFun_pair x x) hn).2 (by rw [← formI_apply, h0, Complex.zero_re])
  refine Subtype.ext (funext fun g => ?_)
  have := h g
  rw [conj_mul_self_re] at this
  exact Complex.normSq_eq_zero.1 this

variable (ψ) in

def cK (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (K : Subgroup (GL (Fin m) k)) : ℂ :=
  formI ψ I (delta ψ K) (delta ψ K)

/- English proof (translation)
The claim follows from `formI_self_ne_zero hI (delta_ne_zero hK)`.
-/
theorem cK_ne_zero {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) {K : Subgroup (GL (Fin m) k)}
    (hK : Good ψ K) : cK ψ I K ≠ 0 :=
  formI_self_ne_zero hI (delta_ne_zero hK)

/- English proof (translation)
Rewrite using `[cK, formI_apply, formI_apply]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `h : (delta ψ K' : GL (Fin m) k → ℂ) g = 0`. Simplify using `[h]`.

Rewrite using `[delta_eq_of_le hK hK' hle g h]`.
-/
theorem formI_delta_le (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K)
    (hK' : Good ψ K') (hle : K' ≤ K) : formI ψ I (delta ψ K) (delta ψ K') = cK ψ I K' := by
  rw [cK, formI_apply, formI_apply]
  congr 1
  funext g
  by_cases h : (delta ψ K' : GL (Fin m) k → ℂ) g = 0
  · simp [h]
  · rw [delta_eq_of_le hK hK' hle g h]

/- English proof (translation)
Establish `hK'` using `good_conj hK hu`. Establish `hfix : ∀ κ ∈ K, rhoW ψ κ (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom))) = rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom))`. Introduce `κ hκ`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Establish `e1 : κ * u⁻¹ = u⁻¹ * (u * κ * u⁻¹)` using `by group`.

Establish `e2 : u⁻¹ * (u * κ * u⁻¹) * u = κ` using `by group`. Rewrite using `[e1, map_mul, Module.End.mul_apply, rhoW_delta (mem_conj.2 (by rw [e2]; exact hκ))]`. Establish `hs : ∀ g, (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) : GL (Fin m) k → ℂ) g ≠ 0 → ∃ n ∈ unipB k (Fin m), ∃ κ ∈ K, g = n * κ`. Introduce `g hg`. Rewrite `hg` using `[rhoW_apply]`.

Choose the witnesses or unpack the hypotheses as in `⟨n, hn, κ', hκ', he⟩ : ∃ n ∈ unipB k (Fin m), ∃ κ' ∈ K.map (MulAut.conj u).toMonoidHom, g * u⁻¹ = n * κ' := by`. Assume the negation of the conclusion as `h`. Conclude with `hg (delta_eq_zero h)`. Use `⟨n * u, (unipB k (Fin m)).mul_mem hn hu, u⁻¹ * κ' * u, mem_conj.1 hκ', ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[eq_smul_delta hK _ hfix hs, rhoW_apply, one_mul]`. Use `congr 1`. Use `delta_mul hK' ((unipB k (Fin m)).inv_mem hu) (K.map (MulAut.conj u).toMonoidHom).one_mem` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this, superDiag_inv hu, AddChar.inv_apply]`.
-/
theorem rhoW_inv_delta_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) :
    rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) =
      ((ψ⁻¹ (superDiag u) : Circle) : ℂ) • delta ψ K := by
  have hK' := good_conj hK hu
  have hfix : ∀ κ ∈ K, rhoW ψ κ (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom))) =
      rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) := by
    intro κ hκ
    rw [← Module.End.mul_apply, ← map_mul]
    have e1 : κ * u⁻¹ = u⁻¹ * (u * κ * u⁻¹) := by group
    have e2 : u⁻¹ * (u * κ * u⁻¹) * u = κ := by group
    rw [e1, map_mul, Module.End.mul_apply, rhoW_delta (mem_conj.2 (by rw [e2]; exact hκ))]
  have hs : ∀ g, (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) : GL (Fin m) k → ℂ) g ≠ 0 →
      ∃ n ∈ unipB k (Fin m), ∃ κ ∈ K, g = n * κ := by
    intro g hg
    rw [rhoW_apply] at hg
    obtain ⟨n, hn, κ', hκ', he⟩ : ∃ n ∈ unipB k (Fin m), ∃ κ' ∈ K.map (MulAut.conj u).toMonoidHom,
        g * u⁻¹ = n * κ' := by
      by_contra h
      exact hg (delta_eq_zero h)
    refine ⟨n * u, (unipB k (Fin m)).mul_mem hn hu, u⁻¹ * κ' * u, mem_conj.1 hκ', ?_⟩
    calc g = g * u⁻¹ * u := by group
      _ = n * κ' * u := by rw [he]
      _ = n * u * (u⁻¹ * κ' * u) := by group
  rw [eq_smul_delta hK _ hfix hs, rhoW_apply, one_mul]
  congr 1
  have := delta_mul hK' ((unipB k (Fin m)).inv_mem hu) (K.map (MulAut.conj u).toMonoidHom).one_mem
  rw [mul_one] at this
  rw [this, superDiag_inv hu, AddChar.inv_apply]

end DiscreteGroups.sglob.LConv

end
