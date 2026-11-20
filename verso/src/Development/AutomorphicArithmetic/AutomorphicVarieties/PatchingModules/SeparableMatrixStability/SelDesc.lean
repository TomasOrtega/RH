import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Take `⟨N, hN⟩` from `ht`. Establish `hI : Ideal.span {t} ^ N = ⊥`. Rewrite using `[Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]`. Establish `hle' : H.comap h.p ≤ G.η.ker` using `fun a ha => by`. Rewrite using `[MonoidHom.mem_ker, ← h.η a]`.

Conclude with `hle ha`. Establish `hmul : ∀ a b : G.G₀, ρ (h.p₀ (a * b)) = ρ (h.p₀ a) * ρ (h.p₀ b)` using `fun a b => by`. Rewrite using `[map_mul, hm]`. Establish `hρc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ (h.p₀ a) i j` using `fun i j => (h.adicCont_iff _ (fun c => ρ c i j)).2 (hc i j)`. Establish `hun : ∀ (m : ℕ) (k : G.G₀), (k : G.Γ) ∈ H.comap h.p → ∃ e, ∀ i j, (ρ (h.p₀ (k ^ l ^ e)) - 1) i j ∈ Ideal.span {t} ^ m`.

Introduce `m k hk'`. Take `⟨e, he⟩` from `hu (h.p₀ k) hk'`. Conclude with `⟨e, fun i j => by rw [map_pow, he, sub_self]; exact Submodule.zero_mem _⟩`. Establish `hcoc` using `(coc_pl l L G n R (Ideal.span {t}) (fun a => ρ (h.p₀ a)) z (H.comap h.p) (ho.preimage h.cont) hle' hl (by simp [h1]) hmul hρc hun hzc hz).2`. Establish `hzero : ∀ k : G.G₀, g.p₀ k = 1 → z k = 0`.

Introduce `k hk1`. Establish `hmem : (k : G.Γ) ∈ PL l (H.comap h.p)`. Rewrite using `[← hk, MonoidHom.mem_ker]`. Conclude with `congrArg Subtype.val hk1`. Use extensionality with `i j`.

Establish `hz0` using `(hcoc k hmem N i j).2`. Rewrite `hz0` using `[hI, Ideal.mem_bot]`. Simplify using `using hz0`. Use `⟨fun c => z (Classical.choose (g.p₀_surj c)), funext fun a => ?_⟩` and prove the remaining obligations. Take `hb'` from `Classical.choose_spec (g.p₀_surj (g.p₀ a))`.

Use `show z a = z (Classical.choose (g.p₀_surj (g.p₀ a)))`. Generalize the expression as in `Classical.choose (g.p₀_surj (g.p₀ a)) = b at hb' ⊢`. Establish `hk1 : g.p₀ (a⁻¹ * b) = 1` using `by rw [map_mul, map_inv, hb', inv_mul_cancel]`. Establish `hab : b = a * (a⁻¹ * b)` using `by group`. Rewrite using `[hab, hz, hzero _ hk1]`.

Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.Pa.sel_desc_fac {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G0 : Glob l L} (g : G.Hom G') (h : G.Hom G0)
    {n : ℕ} {R : Type} [CommRing R] (t : R) (ht : IsNilpotent t) (hl : (l : R) = 0)
    (H : Subgroup G0.Γ) [H.Normal] (ho : IsOpen (H : Set G0.Γ)) (hle : H ≤ G0.η.ker)
    (hk : g.p.ker = PL l (H.comap h.p))
    (ρ : G0.G₀ → Matrix (Fin n) (Fin n) R) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b)
    (hc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ a i j)
    (hu : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, ρ (a ^ l ^ e) = 1)
    (z : G.G₀ → Matrix (Fin n) (Fin n) R) (hzc : ∀ i j, AdicCont (Ideal.span {t}) fun a => z a i j)
    (hz : ∀ a b, z (a * b) = z a + ρ (h.p₀ a) * z b * ρ (h.p₀ a⁻¹)) :
    ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) R, z = fun a => z' (g.p₀ a) := by
  obtain ⟨N, hN⟩ := ht
  have hI : Ideal.span {t} ^ N = ⊥ := by
    rw [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]
  have hle' : H.comap h.p ≤ G.η.ker := fun a ha => by
    rw [MonoidHom.mem_ker, ← h.η a]
    exact hle ha
  have hmul : ∀ a b : G.G₀, ρ (h.p₀ (a * b)) = ρ (h.p₀ a) * ρ (h.p₀ b) := fun a b => by
    rw [map_mul, hm]
  have hρc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ (h.p₀ a) i j := fun i j =>
    (h.adicCont_iff _ (fun c => ρ c i j)).2 (hc i j)
  have hun : ∀ (m : ℕ) (k : G.G₀), (k : G.Γ) ∈ H.comap h.p →
      ∃ e, ∀ i j, (ρ (h.p₀ (k ^ l ^ e)) - 1) i j ∈ Ideal.span {t} ^ m := by
    intro m k hk'
    obtain ⟨e, he⟩ := hu (h.p₀ k) hk'
    exact ⟨e, fun i j => by rw [map_pow, he, sub_self]; exact Submodule.zero_mem _⟩
  have hcoc := (coc_pl l L G n R (Ideal.span {t}) (fun a => ρ (h.p₀ a)) z (H.comap h.p)
    (ho.preimage h.cont) hle' hl (by simp [h1]) hmul hρc hun hzc hz).2
  have hzero : ∀ k : G.G₀, g.p₀ k = 1 → z k = 0 := by
    intro k hk1
    have hmem : (k : G.Γ) ∈ PL l (H.comap h.p) := by
      rw [← hk, MonoidHom.mem_ker]
      exact congrArg Subtype.val hk1
    ext i j
    have hz0 := (hcoc k hmem N i j).2
    rw [hI, Ideal.mem_bot] at hz0
    simpa using hz0
  refine ⟨fun c => z (Classical.choose (g.p₀_surj c)), funext fun a => ?_⟩
  obtain hb' := Classical.choose_spec (g.p₀_surj (g.p₀ a))
  show z a = z (Classical.choose (g.p₀_surj (g.p₀ a)))
  generalize Classical.choose (g.p₀_surj (g.p₀ a)) = b at hb' ⊢
  have hk1 : g.p₀ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hb', inv_mul_cancel]
  have hab : b = a * (a⁻¹ * b) := by group
  rw [hab, hz, hzero _ hk1]
  simp

/- English proof (translation)
Use extensionality with `i j`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp (ha i j)`. Establish `h0 : algebraMap x.A X ((mat x.ρ a - 1) i j) = 0`. Rewrite using `[← hc, map_mul, hX, mul_zero]`. Rewrite `h0` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`.

Simplify using `only [NP.ρX, Matrix.map_apply]`. Rewrite using `[h0, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem UpperTheory.V.Pa.sel_desc_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (m : ℕ)
    (X : Type) [CommRing X] [Algebra x.A X] (hX : algebraMap x.A X (x.t ^ m) = 0) (a : F.G₀)
    (ha : ∀ i j, (mat x.ρ a - 1) i j ∈ Ideal.span {x.t ^ m}) : x.ρX X a = 1 := by
  ext i j
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha i j)
  have h0 : algebraMap x.A X ((mat x.ρ a - 1) i j) = 0 := by
    rw [← hc, map_mul, hX, mul_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  simp only [NP.ρX, Matrix.map_apply]
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Apply `DD.ext` to reduce the goal to its premises. Use `show (0 : X) * 0 = 0`.

Simplify using the standard rewrite rules. Use `show (fun r => (0 : X) * Z r c j + Z r i c * 0) = 0`. Use function extensionality and compare the values at `r`. Simplify using the standard rewrite rules. Use `show (fun r => (0 : X) * (0 : Fin g → X) r + (0 : Fin g → X) r * 0) = 0`.

Use function extensionality and compare the values at `r`. Simplify using the standard rewrite rules. Use `show (0 : X) * 0 + 0 * 0 + ∑ r, (Z r i c * (0 : Fin g → X) r + (0 : Fin g → X) r * Z r c j) = 0`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.V.Pa.epM_mul_self_eq_zero (X : Type) [CommRing X] (g n : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  apply DD.ext
  · show (0 : X) * 0 = 0
    simp
  · show (fun r => (0 : X) * Z r c j + Z r i c * 0) = 0
    funext r
    simp
  · show (fun r => (0 : X) * (0 : Fin g → X) r + (0 : Fin g → X) r * 0) = 0
    funext r
    simp
  · show (0 : X) * 0 + 0 * 0 + ∑ r, (Z r i c * (0 : Fin g → X) r + (0 : Fin g → X) r * Z r c j) = 0
    simp

/- English proof (translation)
Introduce `l _ L G G' G0 g h n x k H _ m ho hle hU hk`. Take `⟨_, _, hnil1, hnil2, hl0, _⟩` from `am_fin l G0.frame n x m k.g`. Establish `hrho` using `rho_hom l G0.frame n x k (x.Am m)`. Establish `hX0 : algebraMap x.A (x.Am m) (x.t ^ m) = 0` using `(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)`. Establish `hl1 : (l : x.Am m) = 0`.

Rewrite using `[← map_natCast (algebraMap x.A (x.Am m)) l, hl0, map_zero]`. Establish `hlD : (l : DD (x.Am m) k.g) = 0`. Rewrite using `[← map_natCast (algebraMap x.A (DD (x.Am m) k.g)) l, hl0, map_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `z hz`.

Take `⟨_, hzc, hzm, _⟩` from `hz`. Use `sel_desc_fac g h (algebraMap x.A (x.Am m) x.t) hnil1 hl1 H ho hle hk (x.ρX (x.Am m)) hrho.1.1 hrho.1.2.1 hrho.1.2.2 ?_ z hzc hzm` and prove the remaining obligations. Introduce `a ha`. Take `⟨e, he⟩` from `hU m a ha`. Conclude with `⟨e, sel_desc_one x m (x.Am m) hX0 _ he⟩`.

Establish `hu2 : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, k.ρ1 (x.Am m) (a ^ l ^ e) = 1`. Introduce `a ha`. Take `⟨e, he⟩` from `hU m a ha`. Establish `hX : algebraMap x.A (DD (x.Am m) k.g) (x.t ^ m) = 0` using `by show DD.C (algebraMap x.A (x.Am m) (x.t ^ m)) = 0`. Rewrite using `[hX0, map_zero]`.

Establish `h1` using `sel_desc_one x m (DD (x.Am m) k.g) hX _ he`. Set `φ : G0.G₀ →* Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)` to `{ toFun := k.ρ1 (x.Am m), map_one' := hrho.2.1.1, map_mul' := hrho.2.1.2.1 }`. Establish `hp : ∀ (b : G0.G₀) (N : ℕ), k.ρ1 (x.Am m) (b ^ N) = k.ρ1 (x.Am m) b ^ N` using `fun b N => map_pow φ b N`. Use `⟨e + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, pow_mul, hp, Kap.ρ1, h1, mul_one]`.

Establish `hE` using `epM_mul_self_eq_zero (x.Am m) k.g n (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m)))`. Generalize the expression as in `DD.epM (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m))) = E at hE ⊢`. Establish `hN : ∀ N : ℕ, (1 + E) ^ N = 1 + N • E`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_zero, add_zero, succ_nsmul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hN]`.

Establish `hlE : l • E = 0` using `Matrix.ext fun i j => by`. Rewrite using `[Matrix.smul_apply, nsmul_eq_mul, hlD, zero_mul, Matrix.zero_apply]`. Rewrite using `[hlE, add_zero]`. Introduce `z hz`. Apply the tactic sequence `rcases hz with hz | hz <;> obtain ⟨_, hzc, hzm, _⟩ := hz <;>`.

Conclude with `sel_desc_fac g h (algebraMap x.A (DD (x.Am m) k.g) x.t) hnil2 hlD H ho hle hk (k.ρ1 (x.Am m)) hrho.2.1.1 hrho.2.1.2.1 hrho.2.1.2.2 hu2 z hzc hzm`.
-/
theorem UpperTheory.V.Pa.sel_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' G0 : Glob l L) (g : G.Hom G') (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (H : Subgroup G0.Γ) [H.Normal] (m : ℕ), IsOpen (H : Set G0.Γ) → H ≤ G0.η.ker → x.UnipOn H → g.p.ker = PL l (H.comap h.p) → (∀ z ∈ SelP h x (x.Am m), ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (x.Am m), z = fun a => z' (g.p₀ a)) ∧ ∀ z ∈ Sel1 h (x.Am m) k ∪ Sel2 h (x.Am m) k, ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g), z = fun a => z' (g.p₀ a) := by
  intro l _ L G G' G0 g h n x k H _ m ho hle hU hk
  obtain ⟨_, _, hnil1, hnil2, hl0, _⟩ := am_fin l G0.frame n x m k.g
  have hrho := rho_hom l G0.frame n x k (x.Am m)
  have hX0 : algebraMap x.A (x.Am m) (x.t ^ m) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)
  have hl1 : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)) l, hl0, map_zero]
  have hlD : (l : DD (x.Am m) k.g) = 0 := by
    rw [← map_natCast (algebraMap x.A (DD (x.Am m) k.g)) l, hl0, map_zero]
  constructor
  · intro z hz
    obtain ⟨_, hzc, hzm, _⟩ := hz
    refine sel_desc_fac g h (algebraMap x.A (x.Am m) x.t) hnil1 hl1 H ho hle hk (x.ρX (x.Am m))
      hrho.1.1 hrho.1.2.1 hrho.1.2.2 ?_ z hzc hzm
    intro a ha
    obtain ⟨e, he⟩ := hU m a ha
    exact ⟨e, sel_desc_one x m (x.Am m) hX0 _ he⟩
  · have hu2 : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, k.ρ1 (x.Am m) (a ^ l ^ e) = 1 := by
      intro a ha
      obtain ⟨e, he⟩ := hU m a ha
      have hX : algebraMap x.A (DD (x.Am m) k.g) (x.t ^ m) = 0 := by
        show DD.C (algebraMap x.A (x.Am m) (x.t ^ m)) = 0
        rw [hX0, map_zero]
      have h1 := sel_desc_one x m (DD (x.Am m) k.g) hX _ he
      let φ : G0.G₀ →* Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) :=
        { toFun := k.ρ1 (x.Am m), map_one' := hrho.2.1.1, map_mul' := hrho.2.1.2.1 }
      have hp : ∀ (b : G0.G₀) (N : ℕ), k.ρ1 (x.Am m) (b ^ N) = k.ρ1 (x.Am m) b ^ N :=
        fun b N => map_pow φ b N
      refine ⟨e + 1, ?_⟩
      rw [pow_succ, pow_mul, hp, Kap.ρ1, h1, mul_one]
      have hE := epM_mul_self_eq_zero (x.Am m) k.g n (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m)))
      generalize DD.epM (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m))) = E at hE ⊢
      have hN : ∀ N : ℕ, (1 + E) ^ N = 1 + N • E := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_zero,
            add_zero, succ_nsmul]
          abel
      rw [hN]
      have hlE : l • E = 0 := Matrix.ext fun i j => by
        rw [Matrix.smul_apply, nsmul_eq_mul, hlD, zero_mul, Matrix.zero_apply]
      rw [hlE, add_zero]
    intro z hz
    rcases hz with hz | hz <;> obtain ⟨_, hzc, hzm, _⟩ := hz <;>
      exact sel_desc_fac g h (algebraMap x.A (DD (x.Am m) k.g) x.t) hnil2 hlD H ho hle hk
        (k.ρ1 (x.Am m)) hrho.2.1.1 hrho.2.1.2.1 hrho.2.1.2.2 hu2 z hzc hzm
