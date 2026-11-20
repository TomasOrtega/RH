import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.JetMatrixAlgebra
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.WspanLeOpCl
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRAddRight

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14
open Formalism.L2.G.Model (Th0 Lin Aa kapR kap thF)
open Formalism.L2.G.Model.TS (fockR)
open Formalism.MainNotions.G.LatticeSystems (la_tw la_tw_det kp_lamAt_antitone)

def TenOp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n' m : ℕ), 1 ≤ m → ∀ (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
    (c : ℕ) (ν : Fin n' → Fin (m + 1) → ℕ), (∀ t, Antitone (ν t)) → (∀ t ∈ TT, ν t 0 ≤ c) → (∀ t, t ∉ TT → ν t = 0) →
    ∀ β ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
    ∀ s ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
      ∃ (L : Finset (List (Fin n' × (Fin (m + 1) × Fin (m + 1))))) (a : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) → K),
        (∀ l ∈ L, (∀ z ∈ l, z.1 ∈ TT) ∧ ∀ t, (l.filter fun z => z.1 = t).length ≤ c) ∧
        ∀ G ∈ Pol K (ι := Fin n') (m + 1) d, (∑ l ∈ L, a l • opWord l G) ∈ Pol K (ι := Fin n') (m + 1) d ∧
          ∀ H ∈ Pol K (ι := Fin n') (m + 1) d,
            fockR (Th0 K m vec G * s) (Th0 K m vec H * β) = fockR (Th0 K m vec (∑ l ∈ L, a l • opWord l G)) (Th0 K m vec H)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons y l ih => show map φ (X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f)) = X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l (map φ f))`. Rewrite using `[map_mul, map_X, ← ih, pderiv_map]`.
-/
theorem map_opWord {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {n' k : ℕ}
    (l : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) R) :
    map φ (opWord l f) = opWord l (map φ f) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    show map φ (X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l f)) = X (y.1, y.2.1) * pderiv (y.1, y.2.2) (opWord l (map φ f))
    rw [map_mul, map_X, ← ih, pderiv_map]

/- English proof (translation)
Introduce `f hf`. Unfold `OpCl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨f0, hf0, l, h1, h2, rfl⟩` from `hy`.

Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hf0`. Rewrite using `[map_opWord]`. Use `Submodule.subset_span ⟨map φ (t • G), ?_, l, h1, h2, rfl⟩` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_OpCl {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ)
    (G : MvPolynomial (Fin n' × Fin k) R) :
    ∀ f ∈ OpCl TT c (Submodule.span R {G}), map φ f ∈ OpCl TT c (Submodule.span R' {map φ G}) := by
  intro f hf
  unfold OpCl at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f0, hf0, l, h1, h2, rfl⟩ := hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hf0
    rw [map_opWord]
    refine Submodule.subset_span ⟨map φ (t • G), ?_, l, h1, h2, rfl⟩
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Take `⟨hb, hdom, hw⟩` from `hW`. Take `⟨_, elast, hc⟩` from `(hb t).1 ht`. Take `⟨_, _, _, hbc⟩` from `hw t ht`. Establish `h01` using `restricted_weight_first_two_eq (by omega : 1 ≤ m) TT lam0 hdom t ht`. Establish `v1 : ((1 : Fin (m + 1)) : ℕ) = 1`.

Rewrite using `[Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)`. Establish `h10 : (1 : Fin (m + 1)) ≠ 0`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[v1]`.

Simplify using `at this`. Establish `hl0 : Fin.last m ≠ 0`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Establish `r1 : restW TT lam0 t 1 = lam0 t 1` using `by simp [restW, flW, Pi.single_eq_of_ne h10]`. Establish `rl : restW TT lam0 t (Fin.last m) = lam0 t (Fin.last m)` using `by simp [restW, flW, Pi.single_eq_of_ne hl0]`. Establish `hc1` using `abs_le.1 (hc 1 (by rw [v1]; omega) (by rw [v1]; omega))`. Establish `key : restW TT lam0 t 0 - restW TT lam0 t (Fin.last m) ≤ c0`.

Rewrite using `[h01, r1, rl, elast]`. Use linear arithmetic over natural numbers and integers. Establish `eX : topW TT (restW TT lam0) t = restW TT lam0 t` using `by simp [topW, ht]`. Unfold `nuOf lamAt`. Rewrite using `[eX]`.

Use `split_ifs`. Use linear arithmetic over natural numbers and integers. Use `show (-restW TT lam0 t (Fin.rev 0) - -restW TT lam0 t (Fin.rev (Fin.last m))).toNat ≤ c0`. Rewrite using `[Fin.rev_last, Fin.rev_zero]`. Use linear arithmetic over natural numbers and integers.
-/
theorem first_weight_le_conductor {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (t : Fin n') (ht : t ∈ TT) :
    nuOf (lamAt (topW TT (restW TT lam0)) t) 0 ≤ c0 := by
  obtain ⟨hb, hdom, hw⟩ := hW
  obtain ⟨_, elast, hc⟩ := (hb t).1 ht
  obtain ⟨_, _, _, hbc⟩ := hw t ht
  have h01 := restricted_weight_first_two_eq (by omega : 1 ≤ m) TT lam0 hdom t ht
  have v1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; rw [v1] at this; simp at this
  have hl0 : Fin.last m ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have r1 : restW TT lam0 t 1 = lam0 t 1 := by simp [restW, flW, Pi.single_eq_of_ne h10]
  have rl : restW TT lam0 t (Fin.last m) = lam0 t (Fin.last m) := by simp [restW, flW, Pi.single_eq_of_ne hl0]
  have hc1 := abs_le.1 (hc 1 (by rw [v1]; omega) (by rw [v1]; omega))
  have key : restW TT lam0 t 0 - restW TT lam0 t (Fin.last m) ≤ c0 := by
    rw [h01, r1, rl, elast]; omega
  have eX : topW TT (restW TT lam0) t = restW TT lam0 t := by simp [topW, ht]
  unfold nuOf lamAt
  rw [eX]
  split_ifs
  · omega
  · show (-restW TT lam0 t (Fin.rev 0) - -restW TT lam0 t (Fin.rev (Fin.last m))).toNat ≤ c0
    rw [Fin.rev_last, Fin.rev_zero]; omega

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `κ β s F`. Establish `hanti` using `kp_lamAt_antitone rest hd`. Establish `hV : Vsp Kf rest = tensorLat Kf Kf (fun t => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt rest t)))`. Unfold `Vsp`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Rewrite using `[if_pos (hanti t)]`. Take `⟨L, a, hL, hmain⟩` from `hT Kf n' m hm (vecE n') TT d c0 (fun t => nuOf (lamAt rest t)) (fun t => Formalism.L2.G.Model.TS.nuOf_antitone (hanti t)) h0 h1 β (hV ▸ β.2) s (hV ▸ s.2)`. Use `set A : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹ with hA`. Use `set A' : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat) with hA'`.

Establish `hAA' : ∀ x, A x * A' x = 1` using `fun x => Formalism.L2.G.Model.Aa_inv_mul _ _ (la_tw_det _ _ _ _ hh)`. Establish `hA'A : ∀ x, A' x * A x = 1` using `fun x => Formalism.L2.G.Model.Aa_mul_inv _ _ (la_tw_det _ _ _ _ hh)`. Use `set G0 := map (kapR hS) (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) with hG0`. Establish `hG0P : G0 ∈ Pol Kf (ι` using `Fin n') (m + 1) d := (Formalism.L2.G.Model.pol_iff hS _ _ _).1 F.2`. Use `set G := Lin A G0 with hG`.

Establish `hGP : G ∈ Pol Kf (ι` using `Fin n') (m + 1) d := Formalism.L2.G.Model.Lin_Pol _ _ hG0P`. Take `⟨hEP, hpair⟩` from `hmain G hGP`. Use `set E0 := ∑ l ∈ L, a l • opWord l G with hE0`. Set `kS : Kf →+* KK O` to `((kap hS).symm : Kf ≃ₐ[O] KK O)`. Establish `hkk : ∀ x : Kf, kapR hS (kS x) = x` using `fun x => (kap hS).apply_symm_apply x`.

Establish `hkk' : ∀ x : KK O, kS (kapR hS x) = x` using `fun x => (kap hS).symm_apply_apply x`. Establish `hmm : ∀ P : MvPolynomial (Fin n' × Fin (m + 1)) Kf, map (kapR hS) (map kS P) = P`. Introduce `P`. Rewrite using `[map_map]`. Establish `: (kapR hS).comp kS = RingHom.id Kf` using `RingHom.ext hkk`.

Rewrite using `[this, map_id]`. Establish `hmm' : map kS G0 = (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))`. Rewrite using `[hG0, map_map]`. Establish `: kS.comp (kapR hS) = RingHom.id (KK O)` using `RingHom.ext hkk'`. Rewrite using `[this, map_id]`.

Set `Fp : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)` to `map kS (Lin A' (κ • E0))`. Establish `hFpP : Fp ∈ Pol (KK O) (ι` using `Fin n') (m + 1) d := by`. Rewrite using `[Formalism.L2.G.Model.pol_iff hS, hmm]`. Conclude with `Formalism.L2.G.Model.Lin_Pol _ _ (Submodule.smul_mem _ _ hEP)`. Establish `hE0cl : κ • E0 ∈ OpCl TT c0 (Submodule.span Kf {G})`.

Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨G, Submodule.mem_span_singleton_self _, l, (hL l hl).1, (hL l hl).2, rfl⟩`. Establish `hback : Lin A' G = G0`. Rewrite using `[hG, Formalism.L2.G.Model.Lin_comp]`. Simplify using `only [hAA']`.

Conclude with `Formalism.L2.G.Model.Lin_one _`. Establish `hcl2 : Lin A' (κ • E0) ∈ OpCl TT c0 (Submodule.span Kf {G0})`. Use `Lin_OpCl A' A hA'A TT c0 _ _ ?_ _ hE0cl` and prove the remaining obligations. Introduce `f hf`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hf`.

Rewrite using `[map_smul, hback]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)`. Use `⟨⟨Fp, hFpP⟩, ?_, ?_⟩` and prove the remaining obligations. Use `map_OpCl kS TT c0 G0 _ hcl2` as an intermediate fact. Rewrite `this` using `[hmm']`.

Conclude with `this`. Introduce `Y`. Establish `hY : (Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Formalism.L2.G.Model.VS Kf m (vecE n') d`. Rewrite using `[VS_eq]`. Conclude with `Y.2`.

Take `⟨H, hH, hYH⟩` from `(Formalism.L2.G.Model.mem_tens_dw Kf m hm (vecE n') d _).1 hY`. Establish `e1 : ((Θ ⟨Fp, hFpP⟩ : Vsp Kf (flW (m` using `m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = κ • Th0 Kf m (vecE n') E0 := by`. Rewrite using `[hΘ ⟨Fp, hFpP⟩]`. Use `show Th0 Kf m (vecE n') (Lin A (map (kapR hS) Fp)) = _`. Rewrite using `[hmm, Formalism.L2.G.Model.Lin_comp]`.

Simplify using `only [hA'A]`. Rewrite using `[Formalism.L2.G.Model.Lin_one, map_smul]`. Establish `e2 : ((Θ F : Vsp Kf (flW (m` using `m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = Th0 Kf m (vecE n') G := hΘ F`. Rewrite using `[e1, e2, hYH, (Formalism.L2.G.Model.TS.fock_pairing_bilinear (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf (Th0 Kf m (vecE n') E0) 0 (Th0 Kf m (vecE n') H) κ).2.1, hpair H hH]`.
-/
theorem opFAt_of_ten (hT : TenOp) {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CharZero Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ} (hm : 1 ≤ m)
    (TT : Finset (Fin n')) (d : Fin n' → ℕ) (rest : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant rest) (c0 : ℕ)
    (h0 : ∀ t ∈ TT, nuOf (lamAt rest t) 0 ≤ c0) (h1 : ∀ t, t ∉ TT → nuOf (lamAt rest t) = 0)
    (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hΘ : IsTrueTheta hS d (flW d) (vecE n') hmat Θ) : OpFAt TT d rest c0 Θ := by
  intro κ β s F
  have hanti := kp_lamAt_antitone rest hd
  have hV : Vsp Kf rest = tensorLat Kf Kf (fun t => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt rest t))) := by
    unfold Vsp
    congr 1
    funext t
    rw [if_pos (hanti t)]
  obtain ⟨L, a, hL, hmain⟩ := hT Kf n' m hm (vecE n') TT d c0 (fun t => nuOf (lamAt rest t))
    (fun t => Formalism.L2.G.Model.TS.nuOf_antitone (hanti t)) h0 h1 β (hV ▸ β.2) s (hV ▸ s.2)
  set A : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat)⁻¹ with hA
  set A' : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := fun x => Aa (vecE n' x) (la_tw ι σ x.val hmat) with hA'
  have hAA' : ∀ x, A x * A' x = 1 := fun x => Formalism.L2.G.Model.Aa_inv_mul _ _ (la_tw_det _ _ _ _ hh)
  have hA'A : ∀ x, A' x * A x = 1 := fun x => Formalism.L2.G.Model.Aa_mul_inv _ _ (la_tw_det _ _ _ _ hh)
  set G0 := map (kapR hS) (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) with hG0
  have hG0P : G0 ∈ Pol Kf (ι := Fin n') (m + 1) d := (Formalism.L2.G.Model.pol_iff hS _ _ _).1 F.2
  set G := Lin A G0 with hG
  have hGP : G ∈ Pol Kf (ι := Fin n') (m + 1) d := Formalism.L2.G.Model.Lin_Pol _ _ hG0P
  obtain ⟨hEP, hpair⟩ := hmain G hGP
  set E0 := ∑ l ∈ L, a l • opWord l G with hE0
  let kS : Kf →+* KK O := ((kap hS).symm : Kf ≃ₐ[O] KK O)
  have hkk : ∀ x : Kf, kapR hS (kS x) = x := fun x => (kap hS).apply_symm_apply x
  have hkk' : ∀ x : KK O, kS (kapR hS x) = x := fun x => (kap hS).symm_apply_apply x
  have hmm : ∀ P : MvPolynomial (Fin n' × Fin (m + 1)) Kf, map (kapR hS) (map kS P) = P := by
    intro P
    rw [map_map]
    have : (kapR hS).comp kS = RingHom.id Kf := RingHom.ext hkk
    rw [this, map_id]
  have hmm' : map kS G0 = (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) := by
    rw [hG0, map_map]
    have : kS.comp (kapR hS) = RingHom.id (KK O) := RingHom.ext hkk'
    rw [this, map_id]
  let Fp : MvPolynomial (Fin n' × Fin (m + 1)) (KK O) := map kS (Lin A' (κ • E0))
  have hFpP : Fp ∈ Pol (KK O) (ι := Fin n') (m + 1) d := by
    rw [Formalism.L2.G.Model.pol_iff hS, hmm]
    exact Formalism.L2.G.Model.Lin_Pol _ _ (Submodule.smul_mem _ _ hEP)
  have hE0cl : κ • E0 ∈ OpCl TT c0 (Submodule.span Kf {G}) := by
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨G, Submodule.mem_span_singleton_self _, l, (hL l hl).1, (hL l hl).2, rfl⟩
  have hback : Lin A' G = G0 := by
    rw [hG, Formalism.L2.G.Model.Lin_comp]
    simp only [hAA']
    exact Formalism.L2.G.Model.Lin_one _
  have hcl2 : Lin A' (κ • E0) ∈ OpCl TT c0 (Submodule.span Kf {G0}) := by
    refine Lin_OpCl A' A hA'A TT c0 _ _ ?_ _ hE0cl
    intro f hf
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hf
    rw [map_smul, hback]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine ⟨⟨Fp, hFpP⟩, ?_, ?_⟩
  · have := map_OpCl kS TT c0 G0 _ hcl2
    rw [hmm'] at this
    exact this
  · intro Y
    have hY : (Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Formalism.L2.G.Model.VS Kf m (vecE n') d := by
      rw [VS_eq]; exact Y.2
    obtain ⟨H, hH, hYH⟩ := (Formalism.L2.G.Model.mem_tens_dw Kf m hm (vecE n') d _).1 hY
    have e1 : ((Θ ⟨Fp, hFpP⟩ : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        κ • Th0 Kf m (vecE n') E0 := by
      rw [hΘ ⟨Fp, hFpP⟩]
      show Th0 Kf m (vecE n') (Lin A (map (kapR hS) Fp)) = _
      rw [hmm, Formalism.L2.G.Model.Lin_comp]
      simp only [hA'A]
      rw [Formalism.L2.G.Model.Lin_one, map_smul]
    have e2 : ((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        Th0 Kf m (vecE n') G := hΘ F
    rw [e1, e2, hYH, (Formalism.L2.G.Model.TS.fock_pairing_bilinear (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf
      (Th0 Kf m (vecE n') E0) 0 (Th0 Kf m (vecE n') H) κ).2.1, hpair H hH]

/- English proof (translation)
Use `⟨1, one_pos, fun C _ => ?_⟩` and prove the remaining obligations. Introduce `p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H hm hhm Θ hΘ`. Establish `hkr : orbitWindowCount r de hh x + 2 * r ≤ (m + 1) - r` using `H.2.2.2.2.2.2.2.1`. Establish `hr2 : 2 ≤ r` using `H.2.1`. Establish `hdom : IsDominant lam0` using `H.2.2.2.2.1.2.1`.

Establish `hS` using `hSet.1`. Establish `: IsFractionRing W Qq` using `hS.frac_alt`. Establish `: CharZero W` using `Formalism.L2.G.Model.TS.charZero_of_irreducible_natCast hS.prime hS.p_unif`. Establish `hinj : Function.Injective (ι.comp (algebraMap W Qq))` using `ι.injective.comp (IsFractionRing.injective W Qq)`. Establish `: CharZero Kf` using `charZero_of_injective_ringHom hinj`.

Use `opFAt_of_ten hT hS (by omega) TT (dT TT lam0) _ (topW_dom TT (restW_dom (by omega) TT lam0 hdom)) c0 (fun t ht => first_weight_le_conductor (by omega) H.2.2.2.2.1 t ht) (fun t ht => ?_) hm hhm Θ hΘ` and prove the remaining obligations. Establish `: topW TT (restW TT lam0) t = 0` using `by simp [topW, ht]`. Rewrite using `[lamAt_zero this, nuOf_zero]`.
-/
theorem restOpF_of_ten (hT : TenOp) : RestOpF := by
  refine ⟨1, one_pos, fun C _ => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H hm hhm Θ hΘ
  have hkr : orbitWindowCount r de hh x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hS := hSet.1
  have : IsFractionRing W Qq := hS.frac_alt
  have : CharZero W := Formalism.L2.G.Model.TS.charZero_of_irreducible_natCast hS.prime hS.p_unif
  have hinj : Function.Injective (ι.comp (algebraMap W Qq)) := ι.injective.comp (IsFractionRing.injective W Qq)
  have : CharZero Kf := charZero_of_injective_ringHom hinj
  refine opFAt_of_ten hT hS (by omega) TT (dT TT lam0) _ (topW_dom TT (restW_dom (by omega) TT lam0 hdom)) c0
    (fun t ht => first_weight_le_conductor (by omega) H.2.2.2.2.1 t ht) (fun t ht => ?_) hm hhm Θ hΘ
  have : topW TT (restW TT lam0) t = 0 := by simp [topW, ht]
  rw [lamAt_zero this, nuOf_zero]

/- English proof (translation)
The claim follows from `restTSOp_of_opF (restOpF_of_ten hT) D CLa Ck Crk Cdeg`.
-/
theorem restTSOp_of_ten (hT : TenOp) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestTSOp D CLa Ck Crk Cdeg :=
  restTSOp_of_opF (restOpF_of_ten hT) D CLa Ck Crk Cdeg

end Formalism.MainNotions.TestSideCounting
