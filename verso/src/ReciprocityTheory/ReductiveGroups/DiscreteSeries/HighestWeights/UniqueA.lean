import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open Formalism.REAL

variable {n : ℕ}

section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)

/- English proof (translation)
Unfold `kSpan`. Conclude with `Submodule.mem_sInf.2 fun _ hS => hS.1`.
-/
lemma uq_mem_kSpan (x : V) : x ∈ kSpan ε F x := by
    unfold kSpan
    exact Submodule.mem_sInf.2 fun _ hS => hS.1

/- English proof (translation)
Unfold `kSpan`. Conclude with `sInf_le ⟨hx, hS⟩`.
-/
lemma uq_kSpan_le {x : V} {S : Submodule ℂ V} (hx : x ∈ S) (hS : KStable ε F S) : kSpan ε F x ≤ S := by
    unfold kSpan
    exact sInf_le ⟨hx, hS⟩

/- English proof (translation)
Introduce `a b hab y hy`. Unfold `kSpan at hy ⊢`. Rewrite `hy`, the goal using `[Submodule.mem_sInf]`. Conclude with `fun S hS => hS.2 a b hab y (hy S hS)`.
-/
lemma uq_kSpan_stable (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  exact fun S hS => hS.2 a b hab y (hy S hS)

end

/- English proof (translation)
Introduce `a b c d hab hcd`. Establish `h0` using `congrArg f (h a b c d hab hcd)`. Simplify using `only [map_sub, map_mul, apply_ite f, map_zero] at h0`. Conclude with `h0`.
-/
lemma uq_kRel_map {A B : Type*} [Ring A] [Ring B] (ε : Fin n → Bool) (F : Fin n → Fin n → A) (f : A →+* B)
    (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by
  intro a b c d hab hcd
  have h0 := congrArg f (h a b c d hab hcd)
  simp only [map_sub, map_mul, apply_ite f, map_zero] at h0
  exact h0

/- English proof (translation)
Introduce `a b c d hab hcd`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `first`. Consider the case `(simp only [Prod.fst_sub, Prod.fst_mul, h a b c d hab hcd, apply_ite Prod.fst, Prod.fst_zero]; done)`. Consider the case `simp [h a b c d hab hcd, apply_ite Prod.fst]`.

Use `first`. Consider the case `(simp only [Prod.snd_sub, Prod.snd_mul, h' a b c d hab hcd, apply_ite Prod.snd, Prod.snd_zero]; done)`. Consider the case `simp [h' a b c d hab hcd, apply_ite Prod.snd]`.
-/
lemma uq_kRel_prod {A B : Type*} [Ring A] [Ring B] (ε : Fin n → Bool) (F : Fin n → Fin n → A)
    (F' : Fin n → Fin n → B) (h : KRel ε F) (h' : KRel ε F') : KRel ε (fun a b => (F a b, F' a b)) := by
  intro a b c d hab hcd
  refine Prod.ext ?_ ?_
  · first
      | (simp only [Prod.fst_sub, Prod.fst_mul, h a b c d hab hcd, apply_ite Prod.fst, Prod.fst_zero]; done)
      | simp [h a b c d hab hcd, apply_ite Prod.fst]
  · first
      | (simp only [Prod.snd_sub, Prod.snd_mul, h' a b c d hab hcd, apply_ite Prod.snd, Prod.snd_zero]; done)
      | simp [h' a b c d hab hcd, apply_ite Prod.snd]

section

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def uqG (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n) :
    Module.End ℂ (WithLp 2 (V × V')) :=
  LinearEquiv.conjRingEquiv (WithLp.linearEquiv 2 ℂ (V × V')).symm
    (LinearMap.prodMapRingHom ℂ V V' (F a b, F' a b))

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma uqG_apply (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n)
    (x : WithLp 2 (V × V')) :
    WithLp.ofLp (uqG F F' a b x) = (F a b (WithLp.ofLp x).1, F' a b (WithLp.ofLp x).2) := rfl

end

section

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

/- English proof (translation)
Take `⟨B, hBdef⟩ : ∃ B : Submodule ℂ P, B = sInf {S : Submodule ℂ P | x ∈ S ∧ ∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S}` from `⟨_, rfl⟩`. Establish `hxB : x ∈ B`. Rewrite using `[hBdef, Submodule.mem_sInf]`. Conclude with `fun S hS => hS.1`. Establish `hlow : ∀ a b, b < a → ε a = ε b → ∀ y ∈ B, G a b y ∈ B`.

Introduce `a b hba hab y hy`. Rewrite `hy`, the goal using `[hBdef, Submodule.mem_sInf]`. Conclude with `fun S hS => hS.2 a b hba hab y (hy S hS)`. Establish `hBle : ∀ S : Submodule ℂ P, x ∈ S → (∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S) → B ≤ S`. Introduce `S hxS hS`.

Rewrite using `[hBdef]`. Conclude with `sInf_le ⟨hxS, hS⟩`. Establish `hBst : KStable ε G B`. Establish `key : B ≤ B ⊓ ⨅ c : Fin n, ⨅ d : Fin n, ⨅ (_ : ε c = ε d), B.comap (G c d)`. Use `hBle _ ?_ ?_` and prove the remaining obligations.

Use `Submodule.mem_inf.2 ⟨hxB, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap]`. Introduce `c d hcd`. Break down `lt_trichotomy c d with hlt | heq | hgt` into its components or cases. Rewrite using `[hx.2 c d hlt hcd]`.

Conclude with `B.zero_mem`. Substitute `heq` using the available equality. Rewrite using `[hx.1 c]`. Conclude with `B.smul_mem _ hxB`. Conclude with `hlow c d hgt hcd x hxB`.

Introduce `a b hba hab y hy`. Rewrite `hy`, the goal using `[Submodule.mem_inf]`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢`. Use `⟨hlow a b hba hab y hy.1, fun c d hcd => ?_⟩` and prove the remaining obligations. Establish `hcomm : G c d (G a b y) - G a b (G c d y) = (if d = a then G c b else 0) y - (if b = c then G a d else 0) y` using `LinearMap.congr_fun (hR c d a b hcd hab) y`.

Establish `he : G c d (G a b y) = G a b (G c d y) + ((if d = a then G c b else 0) y - (if b = c then G a d else 0) y)`. Rewrite using `[← hcomm]`. Normalize the expressions using the abelian group laws. Rewrite using `[he]`. Use `B.add_mem (hlow a b hba hab _ (hy.2 c d hcd)) (B.sub_mem ?_ ?_)` and prove the remaining obligations.

Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `hy.2 c b (hcd.trans hab)`. Simplify using `using B.zero_mem`. Use `split_ifs with h`.

Substitute `h` using the available equality. Conclude with `hy.2 a d (hab.trans hcd)`. Simplify using `using B.zero_mem`. Introduce `a b hab y hy`. Establish `hy'` using `key hy`.

Rewrite `hy'` using `[Submodule.mem_inf]`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap] at hy'`. Conclude with `hy'.2 a b hab`. Establish `hMB : kSpan ε G x ≤ B` using `uq_kSpan_le ε G hxB hBst`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨N, hNdef⟩ : ∃ N : Submodule ℂ P, N = LinearMap.ker p ⊓ kSpan ε G x` from `⟨_, rfl⟩`. Establish `hNst : KStable ε G N`. Introduce `a b hab z hz`. Rewrite `hz`, the goal using `[hNdef, Submodule.mem_inf, LinearMap.mem_ker]`. Conclude with `⟨by rw [hp a b hab z, hz.1, map_zero], uq_kSpan_stable ε G x a b hab z hz.2⟩`.

Establish `hNo : KStable ε G Nᗮ`. Introduce `a b hab m hm`. Rewrite `hm`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[← hU b a hab.symm u m]`.

Conclude with `hm _ (hNst b a hab.symm u hu)`. Establish `hzero : ∀ v, v ∈ N → v ∈ Nᗮ → v = 0` using `fun v h1 h2 => inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 v h1)`. Take `⟨nn, hnn, mm, hmm, hxnm⟩ : ∃ y ∈ N, ∃ z ∈ Nᗮ, x = y + z` from `by first`. Consider the case `exact N.exists_add_mem_mem_orthogonal x`. Consider the case `(obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (show x ∈ N ⊔ Nᗮ by rw [Submodule.sup_orthogonal_of_completeSpace]; exact Submodule.mem_top)`.

Conclude with `⟨y, hy, z, hz, e.symm⟩)`. Establish `hnr : ∀ c d, c < d → ε c = ε d → G c d nn = 0`. Introduce `c d hcd hε`. Establish `h0 : G c d nn + G c d mm = 0` using `by rw [← map_add, ← hxnm, hx.2 c d hcd hε]`. Establish `h1 : G c d nn = -G c d mm` using `eq_neg_of_add_eq_zero_left h0`.

Use `hzero _ (hNst c d hε nn hnn) ?_` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `Nᗮ.neg_mem (hNo c d hε mm hmm)`. Establish `hnB : nn ∈ B` using `hMB (Submodule.mem_inf.1 (hNdef ▸ hnn)).2`. Establish `hmB : mm ∈ B`.

Establish `hme : mm = x - nn` using `by rw [hxnm]; abel`. Rewrite using `[hme]`. Conclude with `B.sub_mem hxB hnB`. Establish `hS : ∀ y ∈ B, ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ`. Set `S : Submodule ℂ P` to `{ carrier := {y | ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ} add_mem' := by`.

Introduce `y z hy hz`. Simplify using `only [Set.mem_setOf_eq, inner_add_right] at hy hz ⊢`. Rewrite using `[add_mul, mul_add, hy, hz]`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`.

Introduce `c y hy`. Simplify using `only [Set.mem_setOf_eq, inner_smul_right] at hy ⊢`. Rewrite using `[mul_assoc, hy]`. Use `ring }`. Establish `hBS : B ≤ S`.

Use `hBle S ?_ ?_` and prove the remaining obligations. Use `show ⟪nn, x⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, x⟫_ℂ`. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Apply the tactic sequence `first | rfl | simp | norm_cast`. Introduce `a b hba hab y _ show ⟪nn, G a b y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, G a b y⟫_ℂ`.

Rewrite using `[← hU b a hab.symm nn y, ← hU b a hab.symm x y, hnr b a hba hab.symm, hx.2 b a hba hab.symm]`. Simplify using the standard rewrite rules. Conclude with `fun y hy => hBS hy`. Establish `key` using `hS mm hmB`. Establish `hnm : ⟪nn, mm⟫_ℂ = 0` using `(Submodule.mem_orthogonal _ _).1 hmm nn hnn`.

Establish `hnx : ⟪nn, x⟫_ℂ = ⟪nn, nn⟫_ℂ` using `by rw [hxnm, inner_add_right, hnm, add_zero]`. Establish `hxm : ⟪x, mm⟫_ℂ = ⟪mm, mm⟫_ℂ` using `by rw [hxnm, inner_add_left, hnm, zero_add]`. Rewrite `key` using `[hnm, hnx, hxm, zero_mul]`. Establish `hn0 : nn = 0`. Break down `mul_eq_zero.1 key.symm with h | h` into its components or cases.

Conclude with `inner_self_eq_zero.1 h`. It suffices to derive a contradiction. Establish `hm0 : mm = 0` using `inner_self_eq_zero.1 h`. Establish `hxN : x ∈ N` using `by rw [hxnm, hm0, add_zero]; exact hnn`. Rewrite `hxN` using `[hNdef, Submodule.mem_inf, LinearMap.mem_ker]`.

Conclude with `hpx hxN.1`. Establish `hxo : x ∈ Nᗮ` using `by rw [hxnm, hn0, zero_add]; exact hmm`. Establish `hMo : kSpan ε G x ≤ Nᗮ` using `uq_kSpan_le ε G hxo hNo`. Introduce `z₁ z₂ hz`. Establish `hd : (z₁ : P) - z₂ ∈ N`.

Rewrite using `[hNdef, Submodule.mem_inf, LinearMap.mem_ker]`. Use `⟨?_, Submodule.sub_mem _ z₁.2 z₂.2⟩` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Simplify using `using hz`. Establish `h3` using `hzero _ hd (hMo (Submodule.sub_mem _ z₁.2 z₂.2))`.

Conclude with `Subtype.ext (sub_eq_zero.1 h3)`. Introduce `u`. Establish `hT' : kSpan ε F (p x) ≤ (kSpan ε G x).map p`. Use `uq_kSpan_le ε F (Submodule.mem_map_of_mem (uq_mem_kSpan ε G x)) ?_` and prove the remaining obligations. Introduce `a b hab v hv`.

Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hv`. Rewrite using `[← hp a b hab z]`. Conclude with `Submodule.mem_map_of_mem (uq_kSpan_stable ε G x a b hab z hz)`. Rewrite `hT'` using `[hT]`. Take `⟨z, hz, hzu⟩` from `Submodule.mem_map.1 (hT' Submodule.mem_top)`.

Conclude with `⟨⟨z, hz⟩, by simpa using hzu⟩`.
-/
lemma uq_bij {P U : Type} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]
    [AddCommGroup U] [Module ℂ U] (ε : Fin n → Bool) (G : Fin n → Fin n → Module.End ℂ P)
    (F : Fin n → Fin n → Module.End ℂ U) (μ : Fin n → ℝ) (x : P) (hR : KRel ε G) (hU : KUnit ε G)
    (hx : KHighest ε G μ x) (p : P →ₗ[ℂ] U) (hp : ∀ a b, ε a = ε b → ∀ y, p (G a b y) = F a b (p y))
    (hpx : p x ≠ 0) (hT : kSpan ε F (p x) = ⊤) : Function.Bijective (p.domRestrict (kSpan ε G x)) := by

  obtain ⟨B, hBdef⟩ : ∃ B : Submodule ℂ P, B = sInf {S : Submodule ℂ P | x ∈ S ∧
      ∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S} := ⟨_, rfl⟩
  have hxB : x ∈ B := by
    rw [hBdef, Submodule.mem_sInf]; exact fun S hS => hS.1
  have hlow : ∀ a b, b < a → ε a = ε b → ∀ y ∈ B, G a b y ∈ B := by
    intro a b hba hab y hy
    rw [hBdef, Submodule.mem_sInf] at hy ⊢
    exact fun S hS => hS.2 a b hba hab y (hy S hS)
  have hBle : ∀ S : Submodule ℂ P, x ∈ S →
      (∀ a b, b < a → ε a = ε b → ∀ y ∈ S, G a b y ∈ S) → B ≤ S := by
    intro S hxS hS
    rw [hBdef]; exact sInf_le ⟨hxS, hS⟩

  have hBst : KStable ε G B := by
    have key : B ≤ B ⊓ ⨅ c : Fin n, ⨅ d : Fin n, ⨅ (_ : ε c = ε d), B.comap (G c d) := by
      refine hBle _ ?_ ?_
      · refine Submodule.mem_inf.2 ⟨hxB, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro c d hcd
        rcases lt_trichotomy c d with hlt | heq | hgt
        · rw [hx.2 c d hlt hcd]; exact B.zero_mem
        · subst heq; rw [hx.1 c]; exact B.smul_mem _ hxB
        · exact hlow c d hgt hcd x hxB
      · intro a b hba hab y hy
        rw [Submodule.mem_inf] at hy ⊢
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
        refine ⟨hlow a b hba hab y hy.1, fun c d hcd => ?_⟩
        have hcomm : G c d (G a b y) - G a b (G c d y) =
            (if d = a then G c b else 0) y - (if b = c then G a d else 0) y :=
          LinearMap.congr_fun (hR c d a b hcd hab) y
        have he : G c d (G a b y) = G a b (G c d y) +
            ((if d = a then G c b else 0) y - (if b = c then G a d else 0) y) := by
          rw [← hcomm]; abel
        rw [he]
        refine B.add_mem (hlow a b hba hab _ (hy.2 c d hcd)) (B.sub_mem ?_ ?_)
        · split_ifs with h
          · subst h; exact hy.2 c b (hcd.trans hab)
          · simpa using B.zero_mem
        · split_ifs with h
          · subst h; exact hy.2 a d (hab.trans hcd)
          · simpa using B.zero_mem
    intro a b hab y hy
    have hy' := key hy
    rw [Submodule.mem_inf] at hy'
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hy'
    exact hy'.2 a b hab
  have hMB : kSpan ε G x ≤ B := uq_kSpan_le ε G hxB hBst
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hNdef⟩ : ∃ N : Submodule ℂ P, N = LinearMap.ker p ⊓ kSpan ε G x := ⟨_, rfl⟩
    have hNst : KStable ε G N := by
      intro a b hab z hz
      rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker] at hz ⊢
      exact ⟨by rw [hp a b hab z, hz.1, map_zero], uq_kSpan_stable ε G x a b hab z hz.2⟩
    have hNo : KStable ε G Nᗮ := by
      intro a b hab m hm
      rw [Submodule.mem_orthogonal] at hm ⊢
      intro u hu
      rw [← hU b a hab.symm u m]
      exact hm _ (hNst b a hab.symm u hu)
    have hzero : ∀ v, v ∈ N → v ∈ Nᗮ → v = 0 := fun v h1 h2 =>
      inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 h2 v h1)
    obtain ⟨nn, hnn, mm, hmm, hxnm⟩ : ∃ y ∈ N, ∃ z ∈ Nᗮ, x = y + z := by
      first
        | exact N.exists_add_mem_mem_orthogonal x
        | (obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1
              (show x ∈ N ⊔ Nᗮ by rw [Submodule.sup_orthogonal_of_completeSpace]; exact Submodule.mem_top)
           exact ⟨y, hy, z, hz, e.symm⟩)
    have hnr : ∀ c d, c < d → ε c = ε d → G c d nn = 0 := by
      intro c d hcd hε
      have h0 : G c d nn + G c d mm = 0 := by rw [← map_add, ← hxnm, hx.2 c d hcd hε]
      have h1 : G c d nn = -G c d mm := eq_neg_of_add_eq_zero_left h0
      refine hzero _ (hNst c d hε nn hnn) ?_
      rw [h1]; exact Nᗮ.neg_mem (hNo c d hε mm hmm)
    have hnB : nn ∈ B := hMB (Submodule.mem_inf.1 (hNdef ▸ hnn)).2
    have hmB : mm ∈ B := by
      have hme : mm = x - nn := by rw [hxnm]; abel
      rw [hme]; exact B.sub_mem hxB hnB
    have hS : ∀ y ∈ B, ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ := by
      let S : Submodule ℂ P :=
        { carrier := {y | ⟪nn, y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, y⟫_ℂ}
          add_mem' := by
            intro y z hy hz
            simp only [Set.mem_setOf_eq, inner_add_right] at hy hz ⊢
            rw [add_mul, mul_add, hy, hz]
          zero_mem' := by simp
          smul_mem' := by
            intro c y hy
            simp only [Set.mem_setOf_eq, inner_smul_right] at hy ⊢
            rw [mul_assoc, hy]; ring }
      have hBS : B ≤ S := by
        refine hBle S ?_ ?_
        · show ⟪nn, x⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, x⟫_ℂ
          rw [inner_self_eq_norm_sq_to_K]
          first | rfl | simp | norm_cast
        · intro a b hba hab y _
          show ⟪nn, G a b y⟫_ℂ * ((‖x‖ : ℂ) ^ 2) = ⟪nn, x⟫_ℂ * ⟪x, G a b y⟫_ℂ
          rw [← hU b a hab.symm nn y, ← hU b a hab.symm x y, hnr b a hba hab.symm,
            hx.2 b a hba hab.symm]
          simp
      exact fun y hy => hBS hy
    have key := hS mm hmB
    have hnm : ⟪nn, mm⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hmm nn hnn
    have hnx : ⟪nn, x⟫_ℂ = ⟪nn, nn⟫_ℂ := by rw [hxnm, inner_add_right, hnm, add_zero]
    have hxm : ⟪x, mm⟫_ℂ = ⟪mm, mm⟫_ℂ := by rw [hxnm, inner_add_left, hnm, zero_add]
    rw [hnm, hnx, hxm, zero_mul] at key
    have hn0 : nn = 0 := by
      rcases mul_eq_zero.1 key.symm with h | h
      · exact inner_self_eq_zero.1 h
      · exfalso
        have hm0 : mm = 0 := inner_self_eq_zero.1 h
        have hxN : x ∈ N := by rw [hxnm, hm0, add_zero]; exact hnn
        rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker] at hxN
        exact hpx hxN.1
    have hxo : x ∈ Nᗮ := by rw [hxnm, hn0, zero_add]; exact hmm
    have hMo : kSpan ε G x ≤ Nᗮ := uq_kSpan_le ε G hxo hNo
    intro z₁ z₂ hz
    have hd : (z₁ : P) - z₂ ∈ N := by
      rw [hNdef, Submodule.mem_inf, LinearMap.mem_ker]
      refine ⟨?_, Submodule.sub_mem _ z₁.2 z₂.2⟩
      rw [map_sub, sub_eq_zero]; simpa using hz
    have h3 := hzero _ hd (hMo (Submodule.sub_mem _ z₁.2 z₂.2))
    exact Subtype.ext (sub_eq_zero.1 h3)
  · intro u
    have hT' : kSpan ε F (p x) ≤ (kSpan ε G x).map p := by
      refine uq_kSpan_le ε F (Submodule.mem_map_of_mem (uq_mem_kSpan ε G x)) ?_
      intro a b hab v hv
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
      rw [← hp a b hab z]
      exact Submodule.mem_map_of_mem (uq_kSpan_stable ε G x a b hab z hz)
    rw [hT] at hT'
    obtain ⟨z, hz, hzu⟩ := Submodule.mem_map.1 (hT' Submodule.mem_top)
    exact ⟨⟨z, hz⟩, by simpa using hzu⟩

/- English proof (translation)
Establish `hRG : KRel ε (uqG F F')` using `uq_kRel_map ε (fun a b => ((F a b, F' a b) : Module.End ℂ V × Module.End ℂ V')) ((LinearEquiv.conjRingEquiv (WithLp.linearEquiv 2 ℂ (V × V')).symm).toRingHom.comp (LinearMap.prodMapRingHom ℂ V V')) (uq_kRel_prod ε F F' hR hR')`. Establish `hUG : KUnit ε (uqG F F')`. Introduce `a b hab y z`. Simplify using `only [WithLp.prod_inner_apply, uqG_apply]`. Rewrite using `[hU a b hab, hU' a b hab]`.

Establish `hxH : KHighest ε (uqG F F') Λ (WithLp.toLp 2 (w, w'))`. Use `⟨fun a => WithLp.ofLp_injective 2 ?_, fun a b hlt hab => WithLp.ofLp_injective 2 ?_⟩` and prove the remaining obligations. Rewrite using `[uqG_apply]`. Simplify using `[hw.1 a, hw'.1 a]`. Rewrite using `[uqG_apply]`.

Simplify using `[hw.2 a b hlt hab, hw'.2 a b hlt hab]`. Set `p₁ : WithLp 2 (V × V') →ₗ[ℂ] V` to `LinearMap.fst ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap`. Set `p₂ : WithLp 2 (V × V') →ₗ[ℂ] V'` to `LinearMap.snd ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap`. Establish `hp₁ : ∀ y, p₁ y = (WithLp.ofLp y).1` using `fun _ => rfl`. Establish `hp₂ : ∀ y, p₂ y = (WithLp.ofLp y).2` using `fun _ => rfl`.

Apply the tactic sequence `have hb₁ := uq_bij ε (uqG F F') F Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₁ (fun a b hab y => by rw [hp₁, hp₁, uqG_apply] <;> rfl) (by rw [hp₁]; simpa using hw0) (by rw [hp₁]; simpa using hT)`. Apply the tactic sequence `have hb₂ := uq_bij ε (uqG F F') F' Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₂ (fun a b hab y => by rw [hp₂, hp₂, uqG_apply] <;> rfl) (by rw [hp₂]; simpa using hw0') (by rw [hp₂]; simpa using hT')`. Set `e₁` to `LinearEquiv.ofBijective (p₁.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₁`. Set `e₂` to `LinearEquiv.ofBijective (p₂.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₂`. Establish `he₁ : ∀ z, e₁ z = p₁ z` using `fun _ => rfl`.

Establish `he₂ : ∀ z, e₂ z = p₂ z` using `fun _ => rfl`. Use `⟨e₁.symm.trans e₂, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab v`. Establish `hmem : uqG F F' a b ((e₁.symm v : _) : WithLp 2 (V × V')) ∈ kSpan ε (uqG F F') (WithLp.toLp 2 (w, w'))` using `uq_kSpan_stable ε (uqG F F') _ a b hab _ (e₁.symm v).2`. Establish `hv1 : (WithLp.ofLp ((e₁.symm v : _) : WithLp 2 (V × V'))).1 = v`.

Rewrite using `[← hp₁, ← he₁, LinearEquiv.apply_symm_apply]`. Establish `h1 : e₁.symm (F a b v) = ⟨_, hmem⟩`. Rewrite using `[LinearEquiv.symm_apply_eq, he₁]`. Use `show F a b v = p₁ (uqG F F' a b (e₁.symm v))`. Rewrite using `[hp₁, uqG_apply, hv1]`.

Use `show e₂ (e₁.symm (F a b v)) = F' a b (e₂ (e₁.symm v))`. Simplify using `only [h1, he₂, hp₂, uqG_apply]`. Establish `hx : WithLp.toLp 2 (w, w') ∈ kSpan ε (uqG F F') (WithLp.toLp 2 (w, w'))` using `uq_mem_kSpan ε _ _`. Establish `h2 : e₁.symm w = ⟨_, hx⟩`. Apply the tactic sequence `rw [LinearEquiv.symm_apply_eq, he₁, hp₁] <;> simp`.

Use `show e₂ (e₁.symm w) = w'`. Apply the tactic sequence `rw [h2, he₂, hp₂] <;> simp`.
-/
theorem uq_exists_equiv (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
    (F' : Fin n → Fin n → Module.End ℂ V') (Λ : Fin n → ℝ) (w : V) (w' : V')
    (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw0 : w ≠ 0) (hw0' : w' ≠ 0)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗ[ℂ] V', (∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v)) ∧ φ w = w' := by
  classical
  have hRG : KRel ε (uqG F F') :=
    uq_kRel_map ε (fun a b => ((F a b, F' a b) : Module.End ℂ V × Module.End ℂ V'))
      ((LinearEquiv.conjRingEquiv (WithLp.linearEquiv 2 ℂ (V × V')).symm).toRingHom.comp
        (LinearMap.prodMapRingHom ℂ V V')) (uq_kRel_prod ε F F' hR hR')
  have hUG : KUnit ε (uqG F F') := by
    intro a b hab y z
    simp only [WithLp.prod_inner_apply, uqG_apply]
    rw [hU a b hab, hU' a b hab]
  have hxH : KHighest ε (uqG F F') Λ (WithLp.toLp 2 (w, w')) := by
    refine ⟨fun a => WithLp.ofLp_injective 2 ?_, fun a b hlt hab => WithLp.ofLp_injective 2 ?_⟩
    · rw [uqG_apply]
      simp [hw.1 a, hw'.1 a]
    · rw [uqG_apply]
      simp [hw.2 a b hlt hab, hw'.2 a b hlt hab]
  let p₁ : WithLp 2 (V × V') →ₗ[ℂ] V :=
    LinearMap.fst ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap
  let p₂ : WithLp 2 (V × V') →ₗ[ℂ] V' :=
    LinearMap.snd ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap
  have hp₁ : ∀ y, p₁ y = (WithLp.ofLp y).1 := fun _ => rfl
  have hp₂ : ∀ y, p₂ y = (WithLp.ofLp y).2 := fun _ => rfl
  have hb₁ := uq_bij ε (uqG F F') F Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₁
    (fun a b hab y => by rw [hp₁, hp₁, uqG_apply] <;> rfl) (by rw [hp₁]; simpa using hw0)
    (by rw [hp₁]; simpa using hT)
  have hb₂ := uq_bij ε (uqG F F') F' Λ (WithLp.toLp 2 (w, w')) hRG hUG hxH p₂
    (fun a b hab y => by rw [hp₂, hp₂, uqG_apply] <;> rfl) (by rw [hp₂]; simpa using hw0')
    (by rw [hp₂]; simpa using hT')
  let e₁ := LinearEquiv.ofBijective (p₁.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₁
  let e₂ := LinearEquiv.ofBijective (p₂.domRestrict (kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')))) hb₂
  have he₁ : ∀ z, e₁ z = p₁ z := fun _ => rfl
  have he₂ : ∀ z, e₂ z = p₂ z := fun _ => rfl
  refine ⟨e₁.symm.trans e₂, ?_, ?_⟩
  · intro a b hab v
    have hmem : uqG F F' a b ((e₁.symm v : _) : WithLp 2 (V × V')) ∈
        kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')) :=
      uq_kSpan_stable ε (uqG F F') _ a b hab _ (e₁.symm v).2
    have hv1 : (WithLp.ofLp ((e₁.symm v : _) : WithLp 2 (V × V'))).1 = v := by
      rw [← hp₁, ← he₁, LinearEquiv.apply_symm_apply]
    have h1 : e₁.symm (F a b v) = ⟨_, hmem⟩ := by
      rw [LinearEquiv.symm_apply_eq, he₁]
      show F a b v = p₁ (uqG F F' a b (e₁.symm v))
      rw [hp₁, uqG_apply, hv1]
    show e₂ (e₁.symm (F a b v)) = F' a b (e₂ (e₁.symm v))
    simp only [h1, he₂, hp₂, uqG_apply]
  · have hx : WithLp.toLp 2 (w, w') ∈ kSpan ε (uqG F F') (WithLp.toLp 2 (w, w')) :=
      uq_mem_kSpan ε _ _
    have h2 : e₁.symm w = ⟨_, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq, he₁, hp₁] <;> simp
    show e₂ (e₁.symm w) = w'
    rw [h2, he₂, hp₂] <;> simp

/- English proof (translation)
Take `⟨FU, hFUdef⟩ : ∃ FU : Fin n → Fin n → Module.End ℂ (V ⧸ S), FU = fun a b => if h : ε a = ε b then S.mapQ S (F a b) (fun y hy => hS a b h y hy) else 0` from `⟨_, rfl⟩`. Establish `hFU : ∀ a b, ε a = ε b → ∀ y, S.mkQ (F a b y) = FU a b (S.mkQ y)`. Introduce `a b h y`. Rewrite using `[hFUdef]`. Simplify using `only [dif_pos h]`.

Both sides reduce to the same expression. Establish `hTU : kSpan ε FU (S.mkQ w) = ⊤`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `S.mkQ_surjective z`. Establish `hle : kSpan ε F w ≤ (kSpan ε FU (S.mkQ w)).comap S.mkQ` using `uq_kSpan_le ε F (uq_mem_kSpan ε FU (S.mkQ w)) (fun a b h y hy => by show S.mkQ (F a b y) ∈ kSpan ε FU (S.mkQ w)`.

Rewrite using `[hFU a b h y]`. Conclude with `uq_kSpan_stable ε FU (S.mkQ w) a b h _ hy)`. Establish `hy : y ∈ kSpan ε F w` using `by rw [hT]; exact Submodule.mem_top`. Conclude with `hle hy`. Establish `hpw : S.mkQ w ≠ 0`.

Rewrite using `[Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis. Establish `hbij` using `uq_bij ε F FU Λ w hR hU hw S.mkQ (fun a b h y => hFU a b h y) hpw hTU`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Establish `hy' : y ∈ kSpan ε F w` using `by rw [hT]; exact Submodule.mem_top`.

Establish `h0 : (0 : V) ∈ kSpan ε F w` using `Submodule.zero_mem _`. Establish `key` using `hbij.1 (show (S.mkQ.domRestrict (kSpan ε F w)) ⟨y, hy'⟩ = (S.mkQ.domRestrict (kSpan ε F w)) ⟨0, h0⟩ by simpa using hy)`. Rewrite using `[Submodule.mem_bot]`. Conclude with `congrArg Subtype.val key`.
-/
private theorem eq_bot_of_KStable_of_highest_not_mem (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (w : V) (hR : KRel ε F) (hU : KUnit ε F) (hw : KHighest ε F Λ w) (hT : kSpan ε F w = ⊤)
    (S : Submodule ℂ V) (hS : KStable ε F S) (hwS : w ∉ S) : S = ⊥ := by
  classical
  obtain ⟨FU, hFUdef⟩ : ∃ FU : Fin n → Fin n → Module.End ℂ (V ⧸ S), FU = fun a b =>
      if h : ε a = ε b then S.mapQ S (F a b) (fun y hy => hS a b h y hy) else 0 := ⟨_, rfl⟩
  have hFU : ∀ a b, ε a = ε b → ∀ y, S.mkQ (F a b y) = FU a b (S.mkQ y) := by
    intro a b h y
    rw [hFUdef]
    simp only [dif_pos h]
    rfl
  have hTU : kSpan ε FU (S.mkQ w) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := S.mkQ_surjective z
    have hle : kSpan ε F w ≤ (kSpan ε FU (S.mkQ w)).comap S.mkQ :=
      uq_kSpan_le ε F (uq_mem_kSpan ε FU (S.mkQ w)) (fun a b h y hy => by
        show S.mkQ (F a b y) ∈ kSpan ε FU (S.mkQ w)
        rw [hFU a b h y]
        exact uq_kSpan_stable ε FU (S.mkQ w) a b h _ hy)
    have hy : y ∈ kSpan ε F w := by rw [hT]; exact Submodule.mem_top
    exact hle hy
  have hpw : S.mkQ w ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hbij := uq_bij ε F FU Λ w hR hU hw S.mkQ (fun a b h y => hFU a b h y) hpw hTU
  rw [eq_bot_iff]
  intro y hy
  have hy' : y ∈ kSpan ε F w := by rw [hT]; exact Submodule.mem_top
  have h0 : (0 : V) ∈ kSpan ε F w := Submodule.zero_mem _
  have key := hbij.1 (show (S.mkQ.domRestrict (kSpan ε F w)) ⟨y, hy'⟩ =
      (S.mkQ.domRestrict (kSpan ε F w)) ⟨0, h0⟩ by simpa using hy)
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val key

/- English proof (translation)
Establish `hw0 : w ≠ 0` using `by rintro rfl; simp at hw1`. Establish `hw0' : w' ≠ 0` using `by rintro rfl; simp at hw1'`. Take `⟨φ, hφ, hφw⟩` from `uq_exists_equiv ε F F' Λ w w' hR hR' hU hU' hw hw' hw0 hw0' hT hT'`. Take `⟨A, hA⟩ : ∃ A : Module.End ℂ V, A = LinearMap.adjoint (φ : V →ₗ[ℂ] V') ∘ₗ (φ : V →ₗ[ℂ] V')` from `⟨_, rfl⟩`. Establish `hAinner : ∀ u v, ⟪A u, v⟫_ℂ = ⟪φ u, φ v⟫_ℂ`.

Introduce `u v`. Apply the tactic sequence `rw [hA, LinearMap.comp_apply, LinearMap.adjoint_inner_left] <;> rfl`. Establish `hAF : ∀ a b, ε a = ε b → ∀ v, A (F a b v) = F a b (A v)`. Introduce `a b hab v`. Use `ext_inner_right ℂ fun u => ?_` and prove the remaining obligations.

Rewrite using `[hAinner, hφ a b hab, hU' a b hab, ← hφ b a hab.symm, ← hAinner, hU a b hab]`. Use `haveI : Nontrivial V := ⟨⟨w, 0, hw0⟩⟩`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue A`. Establish `hEst : KStable ε F (Module.End.eigenspace A c)`. Introduce `a b hab v hv`.

Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[hAF a b hab, hv, map_smul]`. Establish `hwE : w ∈ Module.End.eigenspace A c`. Assume the negation of the conclusion as `hwE`. Conclude with `(Module.End.hasEigenvalue_iff.1 hc) (eq_bot_of_KStable_of_highest_not_mem ε F Λ w hR hU hw hT _ hEst hwE)`.

Establish `hEtop : ∀ v, A v = c • v`. Introduce `v`. Establish `h` using `uq_kSpan_le ε F hwE hEst`. Rewrite `h` using `[hT]`. Conclude with `Module.End.mem_eigenspace_iff.1 (h Submodule.mem_top)`.

Establish `hc1 : (starRingEnd ℂ) c = 1`. Establish `h1` using `hAinner w w`. Rewrite `h1` using `[hEtop, inner_smul_left, hφw, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hw1, hw1']`. Simplify using `using h1`. Establish `hinner : ∀ u v, ⟪φ u, φ v⟫_ℂ = ⟪u, v⟫_ℂ`.

Introduce `u v`. Rewrite using `[← hAinner, hEtop, inner_smul_left, hc1, one_mul]`. Use `⟨φ.isometryOfInner hinner, fun a b hab v => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `first | exact hφ a b hab v | simpa using hφ a b hab v`. Apply the tactic sequence `first | exact hφw | simpa using hφw`.
-/
theorem uq_exists_isometry (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)
    (F' : Fin n → Fin n → Module.End ℂ V') (Λ : Fin n → ℝ) (w : V) (w' : V')
    (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw1 : ‖w‖ = 1) (hw1' : ‖w'‖ = 1)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗᵢ[ℂ] V', (∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v)) ∧ φ w = w' := by
  classical
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have hw0' : w' ≠ 0 := by rintro rfl; simp at hw1'
  obtain ⟨φ, hφ, hφw⟩ := uq_exists_equiv ε F F' Λ w w' hR hR' hU hU' hw hw' hw0 hw0' hT hT'
  obtain ⟨A, hA⟩ : ∃ A : Module.End ℂ V,
      A = LinearMap.adjoint (φ : V →ₗ[ℂ] V') ∘ₗ (φ : V →ₗ[ℂ] V') := ⟨_, rfl⟩
  have hAinner : ∀ u v, ⟪A u, v⟫_ℂ = ⟪φ u, φ v⟫_ℂ := by
    intro u v
    rw [hA, LinearMap.comp_apply, LinearMap.adjoint_inner_left] <;> rfl
  have hAF : ∀ a b, ε a = ε b → ∀ v, A (F a b v) = F a b (A v) := by
    intro a b hab v
    refine ext_inner_right ℂ fun u => ?_
    rw [hAinner, hφ a b hab, hU' a b hab, ← hφ b a hab.symm, ← hAinner, hU a b hab]
  haveI : Nontrivial V := ⟨⟨w, 0, hw0⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  have hEst : KStable ε F (Module.End.eigenspace A c) := by
    intro a b hab v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hAF a b hab, hv, map_smul]
  have hwE : w ∈ Module.End.eigenspace A c := by
    by_contra hwE
    exact (Module.End.hasEigenvalue_iff.1 hc) (eq_bot_of_KStable_of_highest_not_mem ε F Λ w hR hU hw hT _ hEst hwE)
  have hEtop : ∀ v, A v = c • v := by
    intro v
    have h := uq_kSpan_le ε F hwE hEst
    rw [hT] at h
    exact Module.End.mem_eigenspace_iff.1 (h Submodule.mem_top)
  have hc1 : (starRingEnd ℂ) c = 1 := by
    have h1 := hAinner w w
    rw [hEtop, inner_smul_left, hφw, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hw1,
      hw1'] at h1
    simpa using h1
  have hinner : ∀ u v, ⟪φ u, φ v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    rw [← hAinner, hEtop, inner_smul_left, hc1, one_mul]
  refine ⟨φ.isometryOfInner hinner, fun a b hab v => ?_, ?_⟩
  · first | exact hφ a b hab v | simpa using hφ a b hab v
  · first | exact hφw | simpa using hφw

end

end ReciprocityTheory.ChartRestriction.DS.HW
