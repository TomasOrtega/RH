import Formalism.CoboundaryTransfers.StatementAPI

noncomputable section

namespace Formalism.CoboundaryTransfers

section DiagramChase₂
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Simplify using `only [pow_zero, one_smul]`. Conclude with `Function.bijective_id`. Consider the case `succ n ih`.

Establish `h : (fun x : D => B.Q ^ (n + 1) • x) = (fun x : D => B.Q ^ n • x) ∘ (fun x : D => B.Q • x)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp, pow_succ, mul_smul]`. Rewrite using `[h]`. Conclude with `ih.comp W.Q_bij`.
-/
lemma chase_qpow_bij (W : WachMod B M D) (j : ℕ) :
    Function.Bijective (fun x : D => B.Q ^ j • x) := by
  induction j with
  | zero =>
    simp only [pow_zero, one_smul]
    exact Function.bijective_id
  | succ n ih =>
    have h : (fun x : D => B.Q ^ (n + 1) • x) = (fun x : D => B.Q ^ n • x) ∘ (fun x : D => B.Q • x) := by
      funext x
      simp only [Function.comp, pow_succ, mul_smul]
    rw [h]
    exact ih.comp W.Q_bij

/- English proof (translation)
Use `show B.Q ^ M • (x - y) ∈ W.N`. Rewrite using `[smul_sub]`. Conclude with `W.N.sub_mem hx hy`.
-/
lemma chase_Q_sub (W : WachMod B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) :
    W.QInv (x - y) := by
  show B.Q ^ M • (x - y) ∈ W.N
  rw [smul_sub]
  exact W.N.sub_mem hx hy
/- English proof (translation)
Use `show B.Q ^ M • (r • x) ∈ W.N`. Rewrite using `[algebra_compatible_smul A r x, smul_comm (B.Q ^ M) (algebraMap O A r) x]`. Conclude with `W.N.smul_mem _ hx`.
-/
lemma chase_Q_smul (W : WachMod B M D) (r : O) {x : D} (hx : W.QInv x) : W.QInv (r • x) := by
  show B.Q ^ M • (r • x) ∈ W.N
  rw [algebra_compatible_smul A r x, smul_comm (B.Q ^ M) (algebraMap O A r) x]
  exact W.N.smul_mem _ hx
/- English proof (translation)
Use `show B.Q ^ M • (b • x) ∈ W.N`. Rewrite using `[smul_comm (B.Q ^ M) b x]`. Conclude with `W.N.smul_mem b hx`.
-/
lemma chase_Q_smulA (W : WachMod B M D) (b : A) {x : D} (hx : W.QInv x) : W.QInv (b • x) := by
  show B.Q ^ M • (b • x) ∈ W.N
  rw [smul_comm (B.Q ^ M) b x]
  exact W.N.smul_mem b hx
/- English proof (translation)
Use `show B.Q ^ M • x ∈ W.N`. Conclude with `W.N.smul_mem _ hx`.
-/
lemma chase_Q_N (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv x := by
  show B.Q ^ M • x ∈ W.N
  exact W.N.smul_mem _ hx
/- English proof (translation)
Use `show B.Q ^ M • W.φ x ∈ W.N`. Conclude with `W.φ_N x hx`.
-/
lemma chase_Q_φ (W : WachMod B M D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x) := by
  show B.Q ^ M • W.φ x ∈ W.N
  exact W.φ_N x hx

/- English proof (translation)
Simplify using `only [WachMod.d1, map_smul, smul_sub]`.
-/
lemma WachMod_d1_smul (W : WachMod B M D) (r : O) (y z : D) :
    W.d1 (r • y) (r • z) = r • W.d1 y z := by
  simp only [WachMod.d1, map_smul, smul_sub]
/- English proof (translation)
Simplify using `only [WachMod.d1, map_sub]`. Normalize the expressions using the abelian group laws.
-/
lemma diffOne_sub (W : WachMod B M D) (y z y' z' : D) :
    W.d1 (y - y') (z - z') = W.d1 y z - W.d1 y' z' := by
  simp only [WachMod.d1, map_sub]
  abel
/- English proof (translation)
Establish `hc : ∀ y : D, W.φ (W.γ y) = W.γ (W.φ y)`. Consider the cases of `W`. Use the matching hypothesis. Simplify using `only [WachMod.d1, map_sub, hc]`. Normalize the expressions using the abelian group laws.
-/
lemma WachMod_d1_phi_sub_gamma_sub_eq_zero (W : WachMod B M D) (x : D) : W.d1 (W.φ x - x) (W.γ x - x) = 0 := by
  have hc : ∀ y : D, W.φ (W.γ y) = W.γ (W.φ y) := by
    cases W
    assumption
  simp only [WachMod.d1, map_sub, hc]
  abel
/- English proof (translation)
Establish `hφ : ∀ x, f.f (W.φ x) = W'.φ (f.f x)`. Consider the cases of `f`. Apply the tactic sequence `first | assumption | done`. Establish `hγ : ∀ x, f.f (W.γ x) = W'.γ (f.f x)`. Consider the cases of `f`.

Apply the tactic sequence `first | assumption | done`. Simplify using `only [WachMod.d1, map_sub, hφ, hγ]`.
-/
lemma map_diffOne {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') (y z : D) :
    f.f (W.d1 y z) = W'.d1 (f.f y) (f.f z) := by
  have hφ : ∀ x, f.f (W.φ x) = W'.φ (f.f x) := by
    cases f
    first | assumption | done
  have hγ : ∀ x, f.f (W.γ x) = W'.γ (f.f x) := by
    cases f
    first | assumption | done
  simp only [WachMod.d1, map_sub, hφ, hγ]
/- English proof (translation)
Establish `hN : ∀ x ∈ W.N, f.f x ∈ W'.N`. Consider the cases of `f`. Apply the tactic sequence `first | assumption | done`. Use `show B.Q ^ M • f.f y ∈ W'.N`. Rewrite using `[← map_smul f.f]`.

Conclude with `hN _ hy`.
-/
lemma chase_hom_Q {W : WachMod B M D} {W' : WachMod B M D'} (f : Hom W W') {y : D}
    (hy : W.QInv y) : W'.QInv (f.f y) := by
  have hN : ∀ x ∈ W.N, f.f x ∈ W'.N := by
    cases f
    first | assumption | done
  show B.Q ^ M • f.f y ∈ W'.N
  rw [← map_smul f.f]
  exact hN _ hy

end DiagramChase₂

/- English proof (translation)
Consider the cases of `B`. Use the matching hypothesis.
-/
private lemma exists_phi_X_eq_X_mul {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) :
    ∃ v, B.φ B.X = B.X * v := by
  cases B
  assumption

/- English proof (translation)
Unfold `DiagramChase₂`. Introduce `O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e c hC hR hT`. Unfold `CokerKilled at hC`. Unfold `RatSurj at hR`. Unfold `WachMod.TorsKilled at hT`.

Unfold `Lifts`. Establish `hpφ : ∀ t, S.π.f (W₁.φ t) = W₂.φ (S.π.f t)`. Generalize the expression as in `S.π = g`. Consider the cases of `g`. Use the matching hypothesis.

Establish `hpγ : ∀ t, S.π.f (W₁.γ t) = W₂.γ (S.π.f t)`. Generalize the expression as in `S.π = g`. Consider the cases of `g`. Use the matching hypothesis. Establish `hiN : ∀ t ∈ W₀.N, S.ι.f t ∈ W₁.N`.

Generalize the expression as in `S.ι = g`. Consider the cases of `g`. Use the matching hypothesis. Establish `hpO : ∀ (r : O) (t : D₁), S.π.f (r • t) = r • S.π.f t`. Introduce `r t`.

Use `first`. Consider the case `exact LinearMap.map_smul_of_tower _ r t`. Consider the case `rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]`. Establish `hiO : ∀ (r : O) (t : D₀), S.ι.f (r • t) = r • S.ι.f t`. Introduce `r t`.

Use `first`. Consider the case `exact LinearMap.map_smul_of_tower _ r t`. Consider the case `rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]`. Establish `key : ∀ (w : D₀) (t : D₁), S.ι.f w = B.X • t → ∃ t₀, S.ι.f t₀ = t ∧ w = B.X • t₀`. Introduce `w t h`.

Establish `h0 : S.π.f t = 0`. Apply `W₂.X_inj` to reduce the goal to its premises. Rewrite using `[← map_smul, ← h]`. Conclude with `(S.exact _).2 ⟨w, rfl⟩`. Take `⟨t₀, ht₀⟩` from `(S.exact t).1 h0`.

Use `⟨t₀, ht₀, S.ι_inj ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ht₀, h]`. Establish `qsat : ∀ w : D₀, W₁.QInv (S.ι.f w) → W₀.QInv w`. Introduce `w h`. Use `show B.Q ^ M • w ∈ W₀.N`.

Apply `S.sat` to reduce the goal to its premises. Rewrite using `[map_smul]`. Conclude with `h`. Introduce `y z hyz`. Take `⟨k, y₁, z₁, hc₁, x, hx, hpy₁, hpz₁⟩` from `hR y z hyz`.

Take `⟨⟨hQy, n, hn, rfl⟩, hd⟩` from `hyz`. Take `⟨⟨hQy₁, n₁, hn₁, hz₁⟩, hd₁⟩` from `hc₁`. Take `⟨a, ha, hpa⟩` from `hC (B.Q ^ M • y) hQy`. Take `⟨yt, hyt⟩ : ∃ t, B.Q ^ M • t = a` from `(chase_qpow_bij W₁ M).2 a`. Establish `hQyt : W₁.QInv yt` using `by show B.Q ^ M • yt ∈ W₁.N`.

Rewrite using `[hyt]`. Conclude with `ha`. Establish `hpyt : S.π.f yt = ((B.p : O) ^ e) • y`. Apply `(chase_qpow_bij W₂ M).1` to reduce the goal to its premises. Use `show B.Q ^ M • S.π.f yt = B.Q ^ M • (((B.p : O) ^ e) • y)`.

Rewrite using `[← map_smul S.π.f, hyt, hpa, smul_comm (B.Q ^ M) ((B.p : O) ^ e) y]`. Take `⟨b, hb, hpb⟩` from `hC n hn`. Establish `hpzt : S.π.f (B.X • b) = ((B.p : O) ^ e) • (B.X • n)`. Rewrite using `[map_smul, hpb, smul_comm B.X ((B.p : O) ^ e) n]`. Establish `hω₁ : S.π.f (W₁.d1 yt (B.X • b)) = 0`.

Rewrite using `[map_diffOne, hpyt, hpzt, WachMod_d1_smul, hd, smul_zero]`. Take `⟨ω, hω⟩` from `(S.exact _).1 hω₁`. Take `⟨y', hQy', hγyt⟩` from `W₁.γ_QN yt hQyt`. Take `⟨v, hv⟩` from `exists_phi_X_eq_X_mul B`. Establish `hiω : S.ι.f ω = B.X • (y' - (v • W₁.φ b - b))`.

Rewrite using `[hω, WachMod.d1, hγyt, W₁.φ_smul, hv, mul_smul, smul_sub, smul_sub]`. Establish `hsmem : W₁.QInv (y' - (v • W₁.φ b - b))` using `chase_Q_sub W₁ hQy' (chase_Q_sub W₁ (chase_Q_smulA W₁ v (chase_Q_φ W₁ hb)) (chase_Q_N W₁ hb))`. Take `⟨s₀, hs₀, hωs₀⟩` from `key ω _ hiω`. Establish `hC2 : W₀.C2 ω` using `⟨s₀, qsat s₀ (by rw [hs₀]; exact hsmem), hωs₀⟩`. Take `⟨m, hm, hpm⟩` from `hC x hx`.

Establish `hpu : S.π.f (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • y)`. Rewrite using `[map_sub, map_sub, hpO, hpφ, hpy₁, hpm, map_smul W₂.φ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) y]`. Normalize the expressions using the abelian group laws. Establish `hpv : S.π.f (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • (B.X • n))`. Rewrite using `[map_sub, map_sub, hpO, hpγ, hpz₁, hpm, map_smul W₂.γ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) (B.X • n)]`.

Normalize the expressions using the abelian group laws. Establish `hα0 : S.π.f (((B.p : O) ^ k) • yt - (((B.p : O) ^ e) • y₁ - (W₁.φ m - m))) = 0`. Rewrite using `[map_sub, hpO, hpyt, hpu, sub_self]`. Establish `hβ0 : S.π.f (((B.p : O) ^ k) • (B.X • b) - (((B.p : O) ^ e) • z₁ - (W₁.γ m - m))) = 0`. Rewrite using `[map_sub, hpO, hpzt, hpv, sub_self]`.

Take `⟨α, hα⟩` from `(S.exact _).1 hα0`. Take `⟨β, hβ⟩` from `(S.exact _).1 hβ0`. Establish `hduv : W₁.d1 (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = 0`. Rewrite using `[diffOne_sub, WachMod_d1_smul, hd₁, smul_zero, WachMod_d1_phi_sub_gamma_sub_eq_zero, sub_zero]`. Establish `hdαβ : W₀.d1 α β = ((B.p : O) ^ k) • ω`.

Apply `S.ι_inj` to reduce the goal to its premises. Rewrite using `[map_diffOne, hα, hβ, diffOne_sub, hduv, sub_zero, WachMod_d1_smul, ← hω, hiO]`. Establish `hQu : W₁.QInv (((B.p : O) ^ e) • y₁ - (W₁.φ m - m))` using `chase_Q_sub W₁ (chase_Q_smul W₁ _ hQy₁) (chase_Q_sub W₁ (chase_Q_φ W₁ hm) (chase_Q_N W₁ hm))`. Establish `hQα : W₀.QInv α` using `qsat α (by rw [hα]; exact chase_Q_sub W₁ (chase_Q_smul W₁ _ hQyt) hQu)`. Take `⟨m', hm', hγm⟩` from `W₁.γ_N m hm`.

Establish `hiβ : S.ι.f β = B.X • (((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m'))`. Rewrite using `[hβ, hz₁, hγm, smul_sub, smul_sub, smul_comm B.X ((B.p : O) ^ k) b, smul_comm B.X ((B.p : O) ^ e) n₁]`. Establish `hKb : ((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m') ∈ W₁.N` using `W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hb) (W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hn₁) hm')`. Take `⟨β₀, hβ₀, hββ₀⟩` from `key β _ hiβ`. Establish `hcob : W₀.IsCob2 (((B.p : O) ^ k) • ω)` using `⟨α, β, ⟨hQα, β₀, S.sat β₀ (by rw [hβ₀]; exact hKb), hββ₀⟩, hdαβ.symm⟩`.

Take `⟨α', β', ⟨hQα', n', hn', hβ'⟩, hcω⟩` from `hT ω hC2 ⟨k, hcob⟩`. Use `⟨c • yt - S.ι.f α', c • (B.X • b) - S.ι.f β', ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `chase_Q_sub W₁ (chase_Q_smul W₁ c hQyt) (chase_hom_Q S.ι hQα')`. Use `⟨c • b - S.ι.f n', W₁.N.sub_mem (W₁.N.smul_of_tower_mem c hb) (hiN n' hn'), ?_⟩` and prove the remaining obligations. Rewrite using `[hβ', map_smul, smul_sub, smul_comm B.X c b]`.

Rewrite using `[diffOne_sub, WachMod_d1_smul, ← map_diffOne S.ι α' β', ← hcω, ← hω, hiO, sub_self]`. Rewrite using `[map_sub, hpO, hpyt, (S.exact _).2 ⟨α', rfl⟩, sub_zero, mul_comm, mul_smul]`. Rewrite using `[map_sub, hpO, hpzt, (S.exact _).2 ⟨β', rfl⟩, sub_zero, mul_comm, mul_smul]`.
-/
theorem cocycleLiftOfExact_holds : DiagramChase₂ := by
  unfold DiagramChase₂
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e c hC hR hT
  unfold CokerKilled at hC
  unfold RatSurj at hR
  unfold WachMod.TorsKilled at hT
  unfold Lifts

  have hpφ : ∀ t, S.π.f (W₁.φ t) = W₂.φ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hpγ : ∀ t, S.π.f (W₁.γ t) = W₂.γ (S.π.f t) := by
    generalize S.π = g
    cases g
    assumption
  have hiN : ∀ t ∈ W₀.N, S.ι.f t ∈ W₁.N := by
    generalize S.ι = g
    cases g
    assumption
  have hpO : ∀ (r : O) (t : D₁), S.π.f (r • t) = r • S.π.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]
  have hiO : ∀ (r : O) (t : D₀), S.ι.f (r • t) = r • S.ι.f t := by
    intro r t
    first
    | exact LinearMap.map_smul_of_tower _ r t
    | rw [algebra_compatible_smul A r t, map_smul, ← algebra_compatible_smul A r]

  have key : ∀ (w : D₀) (t : D₁), S.ι.f w = B.X • t → ∃ t₀, S.ι.f t₀ = t ∧ w = B.X • t₀ := by
    intro w t h
    have h0 : S.π.f t = 0 := by
      apply W₂.X_inj
      rw [← map_smul, ← h]
      exact (S.exact _).2 ⟨w, rfl⟩
    obtain ⟨t₀, ht₀⟩ := (S.exact t).1 h0
    refine ⟨t₀, ht₀, S.ι_inj ?_⟩
    rw [map_smul, ht₀, h]
  have qsat : ∀ w : D₀, W₁.QInv (S.ι.f w) → W₀.QInv w := by
    intro w h
    show B.Q ^ M • w ∈ W₀.N
    apply S.sat
    rw [map_smul]
    exact h
  intro y z hyz
  obtain ⟨k, y₁, z₁, hc₁, x, hx, hpy₁, hpz₁⟩ := hR y z hyz
  obtain ⟨⟨hQy, n, hn, rfl⟩, hd⟩ := hyz
  obtain ⟨⟨hQy₁, n₁, hn₁, hz₁⟩, hd₁⟩ := hc₁

  obtain ⟨a, ha, hpa⟩ := hC (B.Q ^ M • y) hQy
  obtain ⟨yt, hyt⟩ : ∃ t, B.Q ^ M • t = a := (chase_qpow_bij W₁ M).2 a
  have hQyt : W₁.QInv yt := by
    show B.Q ^ M • yt ∈ W₁.N
    rw [hyt]
    exact ha
  have hpyt : S.π.f yt = ((B.p : O) ^ e) • y := by
    apply (chase_qpow_bij W₂ M).1
    show B.Q ^ M • S.π.f yt = B.Q ^ M • (((B.p : O) ^ e) • y)
    rw [← map_smul S.π.f, hyt, hpa, smul_comm (B.Q ^ M) ((B.p : O) ^ e) y]
  obtain ⟨b, hb, hpb⟩ := hC n hn
  have hpzt : S.π.f (B.X • b) = ((B.p : O) ^ e) • (B.X • n) := by
    rw [map_smul, hpb, smul_comm B.X ((B.p : O) ^ e) n]
  have hω₁ : S.π.f (W₁.d1 yt (B.X • b)) = 0 := by
    rw [map_diffOne, hpyt, hpzt, WachMod_d1_smul, hd, smul_zero]
  obtain ⟨ω, hω⟩ := (S.exact _).1 hω₁

  obtain ⟨y', hQy', hγyt⟩ := W₁.γ_QN yt hQyt
  obtain ⟨v, hv⟩ := exists_phi_X_eq_X_mul B
  have hiω : S.ι.f ω = B.X • (y' - (v • W₁.φ b - b)) := by
    rw [hω, WachMod.d1, hγyt, W₁.φ_smul, hv, mul_smul, smul_sub, smul_sub]
  have hsmem : W₁.QInv (y' - (v • W₁.φ b - b)) :=
    chase_Q_sub W₁ hQy' (chase_Q_sub W₁ (chase_Q_smulA W₁ v (chase_Q_φ W₁ hb)) (chase_Q_N W₁ hb))
  obtain ⟨s₀, hs₀, hωs₀⟩ := key ω _ hiω
  have hC2 : W₀.C2 ω := ⟨s₀, qsat s₀ (by rw [hs₀]; exact hsmem), hωs₀⟩

  obtain ⟨m, hm, hpm⟩ := hC x hx
  have hpu : S.π.f (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • y) := by
    rw [map_sub, map_sub, hpO, hpφ, hpy₁, hpm, map_smul W₂.φ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) y]
    abel
  have hpv : S.π.f (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = ((B.p : O) ^ k) • (((B.p : O) ^ e) • (B.X • n)) := by
    rw [map_sub, map_sub, hpO, hpγ, hpz₁, hpm, map_smul W₂.γ, smul_add, smul_sub, smul_comm ((B.p : O) ^ e) ((B.p : O) ^ k) (B.X • n)]
    abel
  have hα0 : S.π.f (((B.p : O) ^ k) • yt - (((B.p : O) ^ e) • y₁ - (W₁.φ m - m))) = 0 := by
    rw [map_sub, hpO, hpyt, hpu, sub_self]
  have hβ0 : S.π.f (((B.p : O) ^ k) • (B.X • b) - (((B.p : O) ^ e) • z₁ - (W₁.γ m - m))) = 0 := by
    rw [map_sub, hpO, hpzt, hpv, sub_self]
  obtain ⟨α, hα⟩ := (S.exact _).1 hα0
  obtain ⟨β, hβ⟩ := (S.exact _).1 hβ0
  have hduv : W₁.d1 (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) (((B.p : O) ^ e) • z₁ - (W₁.γ m - m)) = 0 := by
    rw [diffOne_sub, WachMod_d1_smul, hd₁, smul_zero, WachMod_d1_phi_sub_gamma_sub_eq_zero, sub_zero]
  have hdαβ : W₀.d1 α β = ((B.p : O) ^ k) • ω := by
    apply S.ι_inj
    rw [map_diffOne, hα, hβ, diffOne_sub, hduv, sub_zero, WachMod_d1_smul, ← hω, hiO]
  have hQu : W₁.QInv (((B.p : O) ^ e) • y₁ - (W₁.φ m - m)) :=
    chase_Q_sub W₁ (chase_Q_smul W₁ _ hQy₁) (chase_Q_sub W₁ (chase_Q_φ W₁ hm) (chase_Q_N W₁ hm))
  have hQα : W₀.QInv α := qsat α (by rw [hα]; exact chase_Q_sub W₁ (chase_Q_smul W₁ _ hQyt) hQu)
  obtain ⟨m', hm', hγm⟩ := W₁.γ_N m hm
  have hiβ : S.ι.f β = B.X • (((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m')) := by
    rw [hβ, hz₁, hγm, smul_sub, smul_sub, smul_comm B.X ((B.p : O) ^ k) b, smul_comm B.X ((B.p : O) ^ e) n₁]
  have hKb : ((B.p : O) ^ k) • b - (((B.p : O) ^ e) • n₁ - m') ∈ W₁.N :=
    W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hb) (W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hn₁) hm')
  obtain ⟨β₀, hβ₀, hββ₀⟩ := key β _ hiβ
  have hcob : W₀.IsCob2 (((B.p : O) ^ k) • ω) :=
    ⟨α, β, ⟨hQα, β₀, S.sat β₀ (by rw [hβ₀]; exact hKb), hββ₀⟩, hdαβ.symm⟩

  obtain ⟨α', β', ⟨hQα', n', hn', hβ'⟩, hcω⟩ := hT ω hC2 ⟨k, hcob⟩
  refine ⟨c • yt - S.ι.f α', c • (B.X • b) - S.ι.f β', ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact chase_Q_sub W₁ (chase_Q_smul W₁ c hQyt) (chase_hom_Q S.ι hQα')
  · refine ⟨c • b - S.ι.f n', W₁.N.sub_mem (W₁.N.smul_of_tower_mem c hb) (hiN n' hn'), ?_⟩
    rw [hβ', map_smul, smul_sub, smul_comm B.X c b]
  · rw [diffOne_sub, WachMod_d1_smul, ← map_diffOne S.ι α' β', ← hcω, ← hω, hiO, sub_self]
  · rw [map_sub, hpO, hpyt, (S.exact _).2 ⟨α', rfl⟩, sub_zero, mul_comm, mul_smul]
  · rw [map_sub, hpO, hpzt, (S.exact _).2 ⟨β', rfl⟩, sub_zero, mul_comm, mul_smul]

end Formalism.CoboundaryTransfers
