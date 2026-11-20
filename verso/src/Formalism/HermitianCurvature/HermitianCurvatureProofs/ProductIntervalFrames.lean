import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.StatementQ

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

/- English proof (translation)
Rewrite `h`, the goal using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Conclude with `⟨h.1.comp hΦ.1, by rw [hΦ.2.iSup_comp S]; exact h.2⟩`.
-/
theorem isInternal_comp {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup W] [Module ℂ W]
    (Φ : ι → κ) (hΦ : Function.Bijective Φ) (S : κ → Submodule ℂ W) (h : DirectSum.IsInternal S) :
    DirectSum.IsInternal (fun i => S (Φ i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  exact ⟨h.1.comp hΦ.1, by rw [hΦ.2.iSup_comp S]; exact h.2⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n)]`. Simplify using the standard rewrite rules.
-/
theorem prod_Icc_one (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n)]
    simp

abbrev par (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) : M.Par := ⟨n + 1, r, T, T', u, u⟩

/- English proof (translation)
Establish `hj` using `j.isLt`. Simplify using `only [M.rho, M.Par.lo, par, max_self]`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression.
-/
theorem rho_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (ρ : M.Ty (par n r T T' u)) (j : Fin n) :
    M.rho (par n r T T' u) ρ ((j : ℕ) + 1) = u ((j : ℕ) + 2) + 1 / 2 + (((ρ j : Fin _) : ℕ) : ℝ) := by
  have hj := j.isLt
  simp only [M.rho, M.Par.lo, par, max_self]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

/- English proof (translation)
Establish `h1` using `hL j.castSucc`. Establish `h2` using `hL j.succ`. Simplify using `only [Fin.coe_castSucc, Fin.val_succ] at h1 h2`. Establish `hd : (par n r T T' u).hi ((j : ℕ) + 1) - (par n r T T' u).lo ((j : ℕ) + 1) = ((L j.castSucc - L j.succ - 1 : ℤ) : ℝ)`. Simplify using `only [M.Par.hi, M.Par.lo, par, min_self, max_self]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnn : 0 ≤ L j.castSucc - L j.succ - 1` using `by linarith [hg j]`. Simplify using `only [M.Par.wid]`. Rewrite using `[hd, ← Int.floor_toNat, Int.floor_intCast, Int.toNat_of_nonneg hnn]`.
-/
theorem wid_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (L : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc) (j : Fin n) :
    (((par n r T T' u).wid ((j : ℕ) + 1) : ℕ) : ℤ) = L j.castSucc - L j.succ - 1 := by
  have h1 := hL j.castSucc
  have h2 := hL j.succ
  simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
  have hd : (par n r T T' u).hi ((j : ℕ) + 1) - (par n r T T' u).lo ((j : ℕ) + 1) =
      ((L j.castSucc - L j.succ - 1 : ℤ) : ℝ) := by
    simp only [M.Par.hi, M.Par.lo, par, min_self, max_self]
    push_cast
    linarith
  have hnn : 0 ≤ L j.castSucc - L j.succ - 1 := by linarith [hg j]
  simp only [M.Par.wid]
  rw [hd, ← Int.floor_toNat, Int.floor_intCast, Int.toNat_of_nonneg hnn]

/- English proof (translation)
Establish `hint : ∀ j : Fin (n + 1), ∃ N : ℤ, u ((j : ℕ) + 1) - u 1 = (N : ℝ)` using `fun j => hOK.int_u ((j : ℕ) + 1) (by`. Use `j.2` as an intermediate fact. Rewrite using `[mem_Icc]`. Prove the components needed by the constructor for the conclusion. Use linear arithmetic over natural numbers and integers.

Use `show (j : ℕ) + 1 ≤ n + 1 omega)`. Use `choose L hL using hint`. Establish `hgap : ∀ j : Fin n, u ((j : ℕ) + 2) + 1 ≤ u ((j : ℕ) + 1)` using `fun j => by`. Establish `h` using `hOK.gap ((j : ℕ) + 1) (by`. Use `j.2` as an intermediate fact.

Rewrite using `[mem_Icc]`. Prove the components needed by the constructor for the conclusion. Use linear arithmetic over natural numbers and integers. Use `show (j : ℕ) + 1 ≤ n + 1 - 1 omega)`. Simplify using `only [M.Par.lo, M.Par.hi, max_self, min_self] at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc` using `fun j => by`. Establish `h1` using `hL j.castSucc`. Establish `h2` using `hL j.succ`. Simplify using `only [Fin.val_castSucc, Fin.val_succ] at h1 h2`.

Establish `h3` using `hgap j`. Establish `: (L j.succ : ℝ) + 1 ≤ (L j.castSucc : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hanti : StrictAnti L` using `Fin.strictAnti_iff_succ_lt.2 fun j => by have := hg j; omega`. Establish `hw` using `wid_eq n r T T' u L hL hg`.

Use `set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ`. Establish `hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)` using `fun j => by`. Establish `h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ)` using `by exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL j)`. Rewrite using `[hβ, ← h]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨S₀, hint₀, hirr, heig⟩` from `hK Wp n r z e π u β L hz hT hπ hanti hrel he hez hee`. Set `Φ : M.Ty (par n r T T' u) → {M : Fin n → ℤ // Box L M}` to `fun ρ => ⟨fun j => L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ), fun j => by`. Establish `h1` using `(ρ j).2`. Establish `h2` using `hw j`. Prove the components needed by the constructor for the conclusion.

Use `show L j.succ < L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ)`. Use linear arithmetic over natural numbers and integers. Use `show L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ) ≤ L j.castSucc omega⟩`. Establish `hΦ : Function.Bijective Φ`. Prove the components needed by the constructor for the conclusion.

Introduce `ρ ρ' h`. Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun (congrArg Subtype.val h) j`. Simplify using `only [Φ] at h1`. Apply `Fin.ext` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers. Introduce `M`. Use `⟨fun j => ⟨(M.1 j - L j.succ - 1).toNat, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `M.2 j`. Establish `h2` using `hw j`.

Use linear arithmetic over natural numbers and integers. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `h1` using `M.2 j`. Simplify using `only [Φ]`.

Use linear arithmetic over natural numbers and integers. Use `⟨fun ρ => S₀ (Φ ρ), isInternal_comp Φ hΦ S₀ hint₀, fun ρ => hirr (Φ ρ), ?_⟩` and prove the remaining obligations. Introduce `Bs hBs ρ w v hv`. Rewrite using `[heig Bs hBs (Φ ρ) w v hv]`. Use `congr 1`.

Unfold `M.xC cpol`. Rewrite using `[show (par n r T T' u).k - 1 = n from rfl, prod_Icc_one]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[rho_eq]`. Establish `h : (u ((j : ℕ) + 2) : ℂ) - (u 1 : ℂ) = (L j.succ : ℂ)`.

Use `hL j.succ` as an intermediate fact. Simplify using `only [Fin.val_succ] at this`. Conclude with `congrArg (fun x : ℝ => (x : ℂ)) this` after adjusting the coercions. Simplify using `only [shf, Φ, hβ]`. Use `push_cast`.

Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main (hK : BranchingK) (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (hOK : (par n r T T' u).OK)
    (z e : Fin (2 * r + (n + 1) + 1) → ℂ) (π : Mx (n + 1) r → (Wp →L[ℂ] Wp)) (hz : inWb (n + 1) r z)
    (hT : 0 < Tz (n + 1) r z) (hπ : IsType (n + 1) r z π u) (he : inWb (n + 1) r e)
    (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1) :
    ∃ S : M.Ty (par n r T T' u) → Submodule ℂ Wp, DirectSum.IsInternal S ∧
      (∀ ρ, S ρ ≠ ⊥ ∧ ∀ S' : Submodule ℂ Wp, S' ≤ S ρ →
        (∀ h ∈ UWset (n + 1) r z, h *ᵥ e = e → ∀ v ∈ S', π h v ∈ S') → S' = ⊥ ∨ S' = S ρ) ∧
      ∀ Bs : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [z, e] Bs →
        ∀ (ρ : M.Ty (par n r T T' u)) (w : ℂ), ∀ v ∈ S ρ,
        capRep (n + 1) r π Bs w v = M.xC (par n r T T' u) ρ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2) • v := by
  have hint : ∀ j : Fin (n + 1), ∃ N : ℤ, u ((j : ℕ) + 1) - u 1 = (N : ℝ) := fun j =>
    hOK.int_u ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1
        omega)
  choose L hL using hint
  have hgap : ∀ j : Fin n, u ((j : ℕ) + 2) + 1 ≤ u ((j : ℕ) + 1) := fun j => by
    have h := hOK.gap ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1 - 1
        omega)
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at h
    linarith
  have hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc := fun j => by
    have h1 := hL j.castSucc
    have h2 := hL j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have : (L j.succ : ℝ) + 1 ≤ (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by have := hg j; omega
  have hw := wid_eq n r T T' u L hL hg
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL j)
    rw [hβ, ← h]
    ring
  obtain ⟨S₀, hint₀, hirr, heig⟩ := hK Wp n r z e π u β L hz hT hπ hanti hrel he hez hee
  let Φ : M.Ty (par n r T T' u) → {M : Fin n → ℤ // Box L M} := fun ρ =>
    ⟨fun j => L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ), fun j => by
      have h1 := (ρ j).2
      have h2 := hw j
      constructor
      · show L j.succ < L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ)
        omega
      · show L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ) ≤ L j.castSucc
        omega⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro ρ ρ' h
      funext j
      have h1 := congrFun (congrArg Subtype.val h) j
      simp only [Φ] at h1
      apply Fin.ext
      omega
    · intro M
      refine ⟨fun j => ⟨(M.1 j - L j.succ - 1).toNat, ?_⟩, ?_⟩
      · have h1 := M.2 j
        have h2 := hw j
        omega
      · apply Subtype.ext
        funext j
        have h1 := M.2 j
        simp only [Φ]
        omega
  refine ⟨fun ρ => S₀ (Φ ρ), isInternal_comp Φ hΦ S₀ hint₀, fun ρ => hirr (Φ ρ), ?_⟩
  intro Bs hBs ρ w v hv
  rw [heig Bs hBs (Φ ρ) w v hv]
  congr 1
  unfold M.xC cpol
  rw [show (par n r T T' u).k - 1 = n from rfl, prod_Icc_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rho_eq]
  have h : (u ((j : ℕ) + 2) : ℂ) - (u 1 : ℂ) = (L j.succ : ℂ) := by
    have := hL j.succ
    simp only [Fin.val_succ] at this
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  simp only [shf, Φ, hβ]
  push_cast
  rw [← h]
  ring

end Formalism.FourierDecayAlt.P.ProductIntervalFrames

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

/- English proof (translation)
Introduce `hK Wp _ _ _ P hOK hu'`. Take `⟨k, r, T, T', u, u'⟩` from `P`. Simplify using `only at hu'`. Substitute `hu'` using the available equality. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by have := hOK.k_pos; dsimp only at this; omega⟩`.

Introduce `z e π hz hT hπ he hez hee`. Conclude with `ProductIntervalFrames.main hK Wp n r T T' _ hOK z e π hz hT hπ he hez hee`.
-/
theorem qr_branching_of : Qr.BranchingK → Formalism.FourierDecayAlt.Q.Branching := by
  intro hK Wp _ _ _ P hOK hu'
  obtain ⟨k, r, T, T', u, u'⟩ := P
  dsimp only at hu'
  subst hu'
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hOK.k_pos; dsimp only at this; omega⟩
  intro z e π hz hT hπ he hez hee
  exact ProductIntervalFrames.main hK Wp n r T T' _ hOK z e π hz hT hπ he hez hee

end Formalism.FourierDecayAlt.P
