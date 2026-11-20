import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.PCount

namespace IntegralGeneration

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

/- English proof (translation)
Rewrite using `[H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]`.
-/
theorem h_smul_right (x y : V) (c : E) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

/- English proof (translation)
Rewrite using `[H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]`.
-/
theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm y' x]

/- English proof (translation)
Rewrite `hx` using `[M.L.O_def]`. Establish `h1 : IsIntegral 𝒪[F] (g.e x).1`. Use `hx.map (((AlgHom.fst F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])` as an intermediate fact. Simplify using `using this`. Conclude with `(Valuation.integer.integers (valuation F)).mem_of_integral h1`.
-/
theorem fst_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).1 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).1 := by
    have := hx.map (((AlgHom.fst F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

/- English proof (translation)
Rewrite `hx` using `[M.L.O_def]`. Establish `h1 : IsIntegral 𝒪[F] (g.e x).2`. Use `hx.map (((AlgHom.snd F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])` as an intermediate fact. Simplify using `using this`. Conclude with `(Valuation.integer.integers (valuation F)).mem_of_integral h1`.
-/
theorem snd_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).2 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).2 := by
    have := hx.map (((AlgHom.snd F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

/- English proof (translation)
Take `⟨L, s, mu⟩` from `M`. Simplify using `only at hM g ⊢`. Substitute `hM` using the available equality. Conclude with `Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x`.
-/
theorem mem_R_of_split {g : Loc.SplitG M.L} (hM : M.split = some g) (x : E) :
    x ∈ M.R ↔ g.e x ∈ Formalism.FourierDecayAlt.I.orderR (𝒪[F]) (g.q : F) := by
  obtain ⟨L, s, mu⟩ := M
  simp only at hM g ⊢
  subst hM
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x

/- English proof (translation)
Rewrite using `[g.e.commutes]`. Both sides reduce to the same expression.
-/
theorem e_alg (g : Loc.SplitG M.L) (c : F) : g.e (algebraMap F E c) = (c, c) := by
  rw [g.e.commutes]; rfl

/- English proof (translation)
Take `⟨⟨hSD, hF, hF', -, -, hG⟩, hP⟩` from `ht`. Establish `hfL : ∀ a, t.f a ∈ t.abelian₂` using `hF.1.1`. Establish `hfL' : ∀ a, t.f' a ∈ t.abelian₂` using `hF'.1.1`. Establish `hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O` using `fun x hx y hy => (hSD.2.2 x).1 hx y hy`. Establish `hff : ∀ a b : Fin (r + 1), H.h (t.f b) (t.f a) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T else 0`.

Introduce `a b`. Use `split_ifs with hc`. Take `⟨rfl, rfl⟩` from `hc`. Conclude with `hF.2.2.1`. Conclude with `hF.2.1 b a (not_and_or.mp hc).symm`.

Establish `hff' : ∀ a b : Fin (r + 1), H.h (t.f' b) (t.f' a) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T' else 0`. Introduce `a b`. Use `split_ifs with hc`. Take `⟨rfl, rfl⟩` from `hc`. Conclude with `hF'.2.2.1`.

Conclude with `hF'.2.1 b a (not_and_or.mp hc).symm`. Break down `hM : M.split with _ | g` into its components or cases. Establish `hR : M.R = M.L.O` using `by simp only [Loc.Model.R, hM]`. Simplify using `only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]`. Rewrite using `[hR]`.

Conclude with `hint _ (hfL' b) _ (hfL a)`. Take `⟨-, ⟨c, hc⟩, -⟩` from `hG g hM`. Establish `hq : (g.q : F) ≠ 0`. Introduce `h`. Apply `g.q_irr.ne_zero` to reduce the goal to its premises.

Conclude with `h` after adjusting the coercions. Use `set q : F := (g.q : F) with hq_def`. Use `set k : E := algebraMap F E q with hk`. Use `set n : Fin (r + 1) → V := fun a => algebraMap F E q⁻¹ • (t.f' a - t.f a) with hn_def`. Establish `hnL : ∀ a, n a ∈ t.abelian₂` using `fun a => by`.

Use `hP.1 (Sum.inr a)` as an intermediate fact. Simplify `this` using `only [Loc.HermSp.MMfam, hM, Sum.elim_inr]`. Establish `hf' : ∀ a, t.f' a = t.f a + k • n a` using `fun a => by`. Simplify using `only [hn_def, hk, smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]`. Normalize the expressions using the abelian group laws.

Establish `hcjk : M.L.cj k = k` using `M.L.cj.commutes q`. Establish `hek : g.e k = (q, q)` using `e_alg g q`. Establish `E1 : H.h (t.f' b) (t.f a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a)`. Rewrite using `[hf' b, H.h_add_left, H.h_smul_left]`. Establish `E2 : H.h (t.f' a) (t.f b) = H.h (t.f a) (t.f b) + k * H.h (n a) (t.f b)`.

Rewrite using `[hf' a, H.h_add_left, H.h_smul_left]`. Establish `E3 : H.h (t.f' b) (t.f' a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) + k * H.h (t.f b) (n a) + k * k * H.h (n b) (n a)`. Rewrite using `[hf' b, hf' a]`. Simplify using `only [H.h_add_left, H.h_smul_left, h_add_right, h_smul_right, hcjk]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hswap : (g.e (H.h (n a) (t.f b))).2 = (g.e (H.h (t.f b) (n a))).1`. Rewrite using `[H.h_herm (t.f b) (n a), g.e_cj]`. Both sides reduce to the same expression. Establish `hA` using `fst_mem (g := g) (hint _ (hnL b) _ (hfL a))`. Establish `hB` using `snd_mem (g := g) (hint _ (hnL a) _ (hfL b))`.

Establish `hC` using `fst_mem (g := g) (hint _ (hnL b) _ (hnL a))`. Establish `hqq : q * q⁻¹ = 1` using `mul_inv_cancel₀ hq`. Establish `F1 : (g.e (H.h (t.f' b) (t.f a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1`. Rewrite using `[E1]`. Simplify using `only [map_add, map_mul, hek, Prod.fst_add, Prod.fst_mul]`.

Establish `F2 : (g.e (H.h (t.f' a) (t.f b))).2 = (g.e (H.h (t.f a) (t.f b))).2 + q * (g.e (H.h (n a) (t.f b))).2`. Rewrite using `[E2]`. Simplify using `only [map_add, map_mul, hek, Prod.snd_add, Prod.snd_mul]`. Establish `F3 : (g.e (H.h (t.f' b) (t.f' a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 + q * (g.e (H.h (n a) (t.f b))).2 + q * q * (g.e (H.h (n b) (n a))).1`. Rewrite using `[E3, hswap]`.

Simplify using `only [map_add, map_mul, hek, Prod.fst_add, Prod.fst_mul]`. Generalize the expression as in `(g.e (H.h (n b) (t.f a))).1 = A at hA F1 F3`. Generalize the expression as in `(g.e (H.h (n a) (t.f b))).2 = B at hB F2 F3`. Generalize the expression as in `(g.e (H.h (n b) (n a))).1 = C at hC F3`. Simplify using `only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]`.

Rewrite using `[mem_R_of_split hM]`. Distinguish the cases in `hcn : a = Fin.last r ∧ b = Fin.last r`. Take `⟨rfl, rfl⟩` from `hcn`. Establish `h1` using `hff (Fin.last r) (Fin.last r)`. Establish `h1'` using `hff' (Fin.last r) (Fin.last r)`.

Simplify using `only [and_self, if_true] at h1 h1' ⊢`. Rewrite `F1`, `F2`, `F3` using `[h1, map_neg, e_alg]`. Rewrite `F3` using `[h1', map_neg, e_alg]`. Simplify using `only [Prod.fst_neg, Prod.snd_neg] at F1 F2 F3`. Rewrite using `[map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, F1, F2]`.

Use `⟨?_, ?_, -C, neg_mem hC, ?_⟩` and prove the remaining obligations. Simplify using `only [Prod.fst_sub]`. Establish `: (-t.T + q * A) / q - -t.T / q = A` using `by linear_combination A * hqq`. Rewrite using `[this]`. Conclude with `hA`.

Simplify using `only [Prod.snd_sub]`. Establish `: -((-t.T + q * B) / q) - t.T' / q = q * c - B`. Take the linear combination `q⁻¹ * hc + (q * c - B) * hqq`. Rewrite using `[this]`. Conclude with `sub_mem (mul_mem g.q.2 c.2) hB`.

Simplify using `only [Prod.fst_sub, Prod.snd_sub]`. Take the linear combination `(-q⁻¹) * F3 + (-q * C) * hqq`. Establish `h1` using `hff a b`. Establish `h1'` using `hff' a b`. Establish `h2 : H.h (t.f a) (t.f b) = 0`.

Use `hff b a` as an intermediate fact. Rewrite `this` using `[if_neg (by rintro ⟨rfl, rfl⟩; exact hcn ⟨rfl, rfl⟩)]`. Conclude with `this`. Rewrite `h1`, `h1'`, the goal using `[if_neg hcn]`. Rewrite `F1`, `F3` using `[h1, map_zero]`.

Rewrite `F2` using `[h2, map_zero]`. Rewrite `F3` using `[h1', map_zero]`. Simplify using `only [Prod.fst_zero, Prod.snd_zero, zero_add] at F1 F2 F3`. Rewrite using `[sub_zero, AlgEquiv.apply_symm_apply, F1, F2]`. Use `⟨?_, ?_, -C, neg_mem hC, ?_⟩` and prove the remaining obligations.

Establish `: q * A / q = A` using `by linear_combination A * hqq`. Simplify using `only`. Rewrite using `[this]`. Conclude with `hA`. Establish `: -(q * B / q) = -B` using `by linear_combination (-B) * hqq`.

Simplify using `only`. Rewrite using `[this]`. Conclude with `neg_mem hB`. Simplify using `only`. Take the linear combination `(-q⁻¹) * F3 + (-q * C) * hqq`.
-/
theorem zzplus_int {r : ℕ} {t : Loc.Term V M r} (ht : H.IsGeneric t) (a b : Fin (r + 1)) :
    H.ZZplus t a b ∈ M.R := by
  obtain ⟨⟨hSD, hF, hF', -, -, hG⟩, hP⟩ := ht
  have hfL : ∀ a, t.f a ∈ t.abelian₂ := hF.1.1
  have hfL' : ∀ a, t.f' a ∈ t.abelian₂ := hF'.1.1
  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := fun x hx y hy => (hSD.2.2 x).1 hx y hy
  have hff : ∀ a b : Fin (r + 1), H.h (t.f b) (t.f a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF.2.2.1
    · exact hF.2.1 b a (not_and_or.mp hc).symm
  have hff' : ∀ a b : Fin (r + 1), H.h (t.f' b) (t.f' a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T' else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF'.2.2.1
    · exact hF'.2.1 b a (not_and_or.mp hc).symm
  rcases hM : M.split with _ | g
  ·
    have hR : M.R = M.L.O := by simp only [Loc.Model.R, hM]
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [hR]
    exact hint _ (hfL' b) _ (hfL a)
  ·
    obtain ⟨-, ⟨c, hc⟩, -⟩ := hG g hM
    have hq : (g.q : F) ≠ 0 := by
      intro h; apply g.q_irr.ne_zero; exact_mod_cast h
    set q : F := (g.q : F) with hq_def
    set k : E := algebraMap F E q with hk
    set n : Fin (r + 1) → V := fun a => algebraMap F E q⁻¹ • (t.f' a - t.f a) with hn_def
    have hnL : ∀ a, n a ∈ t.abelian₂ := fun a => by
      have := hP.1 (Sum.inr a)
      simpa only [Loc.HermSp.MMfam, hM, Sum.elim_inr] using this
    have hf' : ∀ a, t.f' a = t.f a + k • n a := fun a => by
      simp only [hn_def, hk, smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
      abel
    have hcjk : M.L.cj k = k := M.L.cj.commutes q
    have hek : g.e k = (q, q) := e_alg g q

    have E1 : H.h (t.f' b) (t.f a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) := by
      rw [hf' b, H.h_add_left, H.h_smul_left]
    have E2 : H.h (t.f' a) (t.f b) = H.h (t.f a) (t.f b) + k * H.h (n a) (t.f b) := by
      rw [hf' a, H.h_add_left, H.h_smul_left]
    have E3 : H.h (t.f' b) (t.f' a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) +
        k * H.h (t.f b) (n a) + k * k * H.h (n b) (n a) := by
      rw [hf' b, hf' a]
      simp only [H.h_add_left, H.h_smul_left, h_add_right, h_smul_right, hcjk]
      ring
    have hswap : (g.e (H.h (n a) (t.f b))).2 = (g.e (H.h (t.f b) (n a))).1 := by
      rw [H.h_herm (t.f b) (n a), g.e_cj]; rfl
    have hA := fst_mem (g := g) (hint _ (hnL b) _ (hfL a))
    have hB := snd_mem (g := g) (hint _ (hnL a) _ (hfL b))
    have hC := fst_mem (g := g) (hint _ (hnL b) _ (hnL a))
    have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
    have F1 : (g.e (H.h (t.f' b) (t.f a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 := by
      rw [E1]; simp only [map_add, map_mul, hek, Prod.fst_add, Prod.fst_mul]
    have F2 : (g.e (H.h (t.f' a) (t.f b))).2 = (g.e (H.h (t.f a) (t.f b))).2 + q * (g.e (H.h (n a) (t.f b))).2 := by
      rw [E2]; simp only [map_add, map_mul, hek, Prod.snd_add, Prod.snd_mul]
    have F3 : (g.e (H.h (t.f' b) (t.f' a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 +
        q * (g.e (H.h (n a) (t.f b))).2 + q * q * (g.e (H.h (n b) (n a))).1 := by
      rw [E3, hswap]; simp only [map_add, map_mul, hek, Prod.fst_add, Prod.fst_mul]
    generalize (g.e (H.h (n b) (t.f a))).1 = A at hA F1 F3
    generalize (g.e (H.h (n a) (t.f b))).2 = B at hB F2 F3
    generalize (g.e (H.h (n b) (n a))).1 = C at hC F3
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [mem_R_of_split hM]
    by_cases hcn : a = Fin.last r ∧ b = Fin.last r
    · obtain ⟨rfl, rfl⟩ := hcn
      have h1 := hff (Fin.last r) (Fin.last r)
      have h1' := hff' (Fin.last r) (Fin.last r)
      simp only [and_self, if_true] at h1 h1' ⊢
      rw [h1, map_neg, e_alg] at F1 F2 F3
      rw [h1', map_neg, e_alg] at F3
      simp only [Prod.fst_neg, Prod.snd_neg] at F1 F2 F3
      rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · simp only [Prod.fst_sub]
        have : (-t.T + q * A) / q - -t.T / q = A := by linear_combination A * hqq
        rw [this]; exact hA
      · simp only [Prod.snd_sub]
        have : -((-t.T + q * B) / q) - t.T' / q = q * c - B := by
          linear_combination q⁻¹ * hc + (q * c - B) * hqq
        rw [this]; exact sub_mem (mul_mem g.q.2 c.2) hB
      · simp only [Prod.fst_sub, Prod.snd_sub]
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq
    · have h1 := hff a b
      have h1' := hff' a b
      have h2 : H.h (t.f a) (t.f b) = 0 := by
        have := hff b a
        rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hcn ⟨rfl, rfl⟩)] at this
        exact this
      rw [if_neg hcn] at h1 h1' ⊢
      rw [h1, map_zero] at F1 F3
      rw [h2, map_zero] at F2
      rw [h1', map_zero] at F3
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at F1 F2 F3
      rw [sub_zero, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · have : q * A / q = A := by linear_combination A * hqq
        simp only; rw [this]; exact hA
      · have : -(q * B / q) = -B := by linear_combination (-B) * hqq
        simp only; rw [this]; exact neg_mem hB
      · simp only
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq

end IntegralGeneration

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Introduce `p _ ht a b` and use `IntegralGeneration.zzplus_int (locH Zd p) ht a b`.
-/
theorem intGenP_holds (Zd : LocDat D) : IntGenP Zd :=
  fun p _ ht a b => IntegralGeneration.zzplus_int (locH Zd p) ht a b

end Formalism.L2.SG.Pf.PCount
