import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL)
open scoped Classical

/- English proof (translation)
Establish `hq' : Valued.v q ≠ 0` using `(Valuation.ne_zero_iff _).2 hq`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `hq' (by rw [← hv, map_zero])`. Establish `hai : (a⁻¹).val = t⁻¹ • (1 : Matrix (Fin n) (Fin n) _)` using `Units.inv_eq_of_mul_eq_one_right (by rw [ha]; simp [smul_smul, ht])`.

Establish `hbi : (b⁻¹).val = q⁻¹ • (1 : Matrix (Fin n) (Fin n) _)` using `Units.inv_eq_of_mul_eq_one_right (by rw [hb]; simp [smul_smul, hq])`. Establish `e1 : (a⁻¹ * b).val = (t⁻¹ * q) • (1 : Matrix (Fin n) (Fin n) _)`. Rewrite using `[Units.val_mul, hai, hb]`. Simplify using `[smul_smul, mul_comm]`. Establish `e2 : ((a⁻¹ * b)⁻¹).val = (q⁻¹ * t) • (1 : Matrix (Fin n) (Fin n) _)`.

Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, hbi, ha]`. Simplify using `[smul_smul, mul_comm]`. Establish `v1 : Valued.v (t⁻¹ * q) = 1`. Rewrite using `[map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']`. Establish `v2 : Valued.v (q⁻¹ * t) = 1`.

Rewrite using `[map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']`. Establish `key : ∀ (c : u.adicCompletion E), Valued.v c = 1 → ∀ i j, Valued.v ((c • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E))) i j) ≤ 1`. Introduce `c hc i j`. Rewrite using `[Matrix.smul_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp [hc]`.

Use `(GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `key _ v1 i j`. Rewrite using `[e2]`. Conclude with `key _ v2 i j`.
-/
private theorem scal_mem_KGL {E : Type} [Field E] [NumberField E] {n : ℕ} {u : Plc E}
    (a b : GL (Fin n) (u.adicCompletion E)) (t q : u.adicCompletion E)
    (ha : a.val = t • (1 : Matrix (Fin n) (Fin n) _)) (hb : b.val = q • (1 : Matrix (Fin n) (Fin n) _))
    (hq : q ≠ 0) (hv : Valued.v t = Valued.v q) : a⁻¹ * b ∈ KGL u n := by
  have hq' : Valued.v q ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have ht : t ≠ 0 := by
    rintro rfl
    exact hq' (by rw [← hv, map_zero])
  have hai : (a⁻¹).val = t⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; simp [smul_smul, ht])
  have hbi : (b⁻¹).val = q⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hb]; simp [smul_smul, hq])
  have e1 : (a⁻¹ * b).val = (t⁻¹ * q) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [Units.val_mul, hai, hb]; simp [smul_smul, mul_comm]
  have e2 : ((a⁻¹ * b)⁻¹).val = (q⁻¹ * t) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hbi, ha]; simp [smul_smul, mul_comm]
  have v1 : Valued.v (t⁻¹ * q) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have v2 : Valued.v (q⁻¹ * t) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have key : ∀ (c : u.adicCompletion E), Valued.v c = 1 → ∀ i j,
      Valued.v ((c • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E))) i j) ≤ 1 := by
    intro c hc i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [hc]
  refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]; exact key _ v1 i j
  · rw [e2]; exact key _ v2 i j

/- English proof (translation)
Introduce `hFH hXi hIS hLO E _ _ _ n hn x ζ hζ U W j Up w₀ S Kw hS χ hχ Φ ψ hΦ hψ`. Choose the witnesses or unpack the hypotheses as in `⟨g₀, hg₀⟩ : ∃ g₀, Φ g₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hΦ.ne (funext h)`.

Establish `cancel : ∀ a b : ℂ, a • Φ g₀ = b • Φ g₀ → a = b` using `fun a b h => smul_left_injective ℂ hg₀ h`. Establish `A : ∀ k ∈ lev S Kw, ∀ h : comp w₀ k ∈ Kw w₀, χ ⟨comp w₀ k, h⟩ = 1 → ∀ g, Φ (g * k) = Φ g`. Introduce `k hk h h1 g`. Rewrite using `[hΦ.right k hk h g, h1]`. Simplify using the standard rewrite rules.

Establish `B : ∀ y, (∀ g, Φ (g * ζ y) = Φ g) → ψ y = 1`. Introduce `y hy`. Establish `h` using `hy g₀`. Rewrite `h` using `[hψ]`. Conclude with `Units.ext (cancel _ 1 (by simpa using h))`.

Establish `C : ∀ k : GUf E n, (∀ u, comp u k ∈ KGL u n) → (∀ u ∈ S, comp u k = 1) → k ∈ lev S Kw` using `fun k h1 h2 => mem_lev.2 ⟨hIS E n hn k h1, fun u hu => by rw [h2 u hu]; exact one_mem _, fun u _ _ => h1 u⟩`. Establish `D : ∀ k ∈ lev S Kw, comp w₀ k = 1 → ∀ g, Φ (g * k) = Φ g`. Introduce `k hk h1 g`. Establish `h : comp w₀ k ∈ Kw w₀` using `by rw [h1]; exact one_mem _`. Use `A k hk h ?_ g` and prove the remaining obligations.

Establish `e : (⟨comp w₀ k, h⟩ : Kw w₀) = 1` using `Subtype.ext h1`. Rewrite using `[e, map_one]`. Establish `hKo : IsOpen ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀))`. Establish `e : ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) = Subtype.val '' {k : Kw w₀ | χ k = 1}`. Use extensionality with `a`.

Simplify using `[Subgroup.mem_map, MonoidHom.mem_ker]`. Rewrite using `[e]`. Conclude with `(hS.opn w₀ hS.mem).isOpenMap_subtype_val _ hχ`. Establish `hK'` using `hLO E n S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)) (by`. Introduce `w hw`.

Distinguish the cases in `h : w = w₀`. Substitute `h` using the available equality. Simplify using `using hKo`. Simplify `hS.opn w hw)` using `[Function.update_of_ne h]`. Establish `hker : IsOpen (((ψ⁻¹).ker : Subgroup (Af E)ˣ) : Set (Af E)ˣ)`.

Use `Subgroup.isOpen_mono (H₁ := (lev S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype))).comap ζ) ?_ (hK'.preimage hζ.cont)` and prove the remaining obligations. Introduce `y hy`. Establish `hy'` using `mem_lev.1 (Subgroup.mem_comap.1 hy)`. Establish `h0` using `hy'.2.1 w₀ hS.mem`. Rewrite `h0` using `[Function.update_self]`.

Take `⟨a, ha, hae⟩` from `Subgroup.mem_map.1 h0`. Establish `hl : ζ y ∈ lev S Kw`. Use `mem_lev.2 ⟨hy'.1, fun u hu => ?_, hy'.2.2⟩` and prove the remaining obligations. Distinguish the cases in `h : u = w₀`. Substitute `h` using the available equality.

Rewrite using `[← hae]`. Conclude with `a.2`. Use `hy'.2.1 u hu` as an intermediate fact. Rewrite `this` using `[Function.update_of_ne h]`. Then use the resulting hypothesis. Establish `h1 : ψ y = 1`.

Use `B y fun g => A _ hl (by rw [← hae]; exact a.2) ?_ g` and prove the remaining obligations. Establish `e : (⟨comp w₀ (ζ y), by rw [← hae]; exact a.2⟩ : Kw w₀) = a` using `Subtype.ext hae.symm`. Rewrite using `[e]`. Conclude with `ha`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]`.

Establish `hprin : ∀ k : Eˣ, (((ψ⁻¹) (diagF E k) : ℂˣ) : ℂ) = (∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ)⁻¹`. Introduce `k`. Take `⟨γ, h1, h2⟩` from `hXi E n W j x ζ hζ k`. Establish `e : ((ψ (diagF E k) : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ`. Apply `cancel` to reduce the goal to its premises.

Rewrite using `[← hψ, ← hζ.central, h1, hΦ.left, h2]`. Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e]`. Take `⟨κ, halg, hloc⟩` from `hFH E (ψ⁻¹) (mOf x W j) hker hprin`. Use `⟨κ, halg, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw y hy`.

Establish `h1 : ψ (sgl w y) = 1`. Use `B _ fun g => D _ (C _ (hζ.unit w y hy) fun u hu => hζ.off w y u (hw u hu)) ?_ g` and prove the remaining obligations. Conclude with `hζ.off w y w₀ (hw w₀ hS.mem)`. Rewrite using `[hloc, MonoidHom.inv_apply, h1, inv_one]`. Introduce `w hw hnw z hz g`.

Establish `hv : κ.val w = (ψ (sgl w (atFin w (unif w))))⁻¹` using `by show κ.loc w (atFin w (unif w)) = _`. Rewrite using `[hloc, MonoidHom.inv_apply]`. Establish `hq : ∀ u : Plc E, ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) ≠ 0`. Introduce `u`. Establish `h0 : Ideal.absNorm w.asIdeal ≠ 0`.

Simplify `w.ne_bot` using `[Ideal.absNorm_eq_zero_iff]`. Conclude with `Nat.cast_ne_zero.2 h0`. Establish `hc : ∀ u, comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) ∈ KGL u n ∧ (¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1)`. Introduce `u`. Establish `hoff : ¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1`.

Introduce `h`. Rewrite using `[map_mul, map_inv, hζ.off w _ u h, (hz u).2 h, inv_one, one_mul]`. Use `⟨?_, hoff⟩` and prove the remaining obligations. Distinguish the cases in `h : SameK x (cj u) w`. Take `⟨t, ht, hvt⟩` from `hζ.unif w _ (unif_spec w) hnw u h`.

Rewrite using `[map_mul, map_inv]`. Conclude with `scal_mem_KGL _ _ t _ ht ((hz u).1 h) (hq u) hvt`. Rewrite using `[hoff h]`. Conclude with `one_mem _`. Establish `hk : (ζ (sgl w (atFin w (unif w))))⁻¹ * z ∈ lev S Kw` using `C _ (fun u => (hc u).1) fun u hu => (hc u).2 (hw u hu)`.

Establish `e : z = ζ (sgl w (atFin w (unif w))) * ((ζ (sgl w (atFin w (unif w))))⁻¹ * z)`. Rewrite using `[mul_inv_cancel_left]`. Rewrite using `[e, ← mul_assoc, D _ hk ((hc w₀).2 (hw w₀ hS.mem)), hψ, hv]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pKapOf_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke → UpperTheory.Gal.CertificateRingHomMap.XiZeta → UpperTheory.Gal.CertificateRingHomMap.IntSim → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.KapOf := by
  intro hFH hXi hIS hLO E _ _ _ n hn x ζ hζ U W j Up w₀ S Kw hS χ hχ Φ ψ hΦ hψ
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, Φ g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ.ne (funext h)
  have cancel : ∀ a b : ℂ, a • Φ g₀ = b • Φ g₀ → a = b := fun a b h => smul_left_injective ℂ hg₀ h
  have A : ∀ k ∈ lev S Kw, ∀ h : comp w₀ k ∈ Kw w₀, χ ⟨comp w₀ k, h⟩ = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h h1 g
    rw [hΦ.right k hk h g, h1]
    simp
  have B : ∀ y, (∀ g, Φ (g * ζ y) = Φ g) → ψ y = 1 := by
    intro y hy
    have h := hy g₀
    rw [hψ] at h
    exact Units.ext (cancel _ 1 (by simpa using h))
  have C : ∀ k : GUf E n, (∀ u, comp u k ∈ KGL u n) → (∀ u ∈ S, comp u k = 1) → k ∈ lev S Kw :=
    fun k h1 h2 => mem_lev.2 ⟨hIS E n hn k h1, fun u hu => by rw [h2 u hu]; exact one_mem _, fun u _ _ => h1 u⟩
  have D : ∀ k ∈ lev S Kw, comp w₀ k = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h1 g
    have h : comp w₀ k ∈ Kw w₀ := by rw [h1]; exact one_mem _
    refine A k hk h ?_ g
    have e : (⟨comp w₀ k, h⟩ : Kw w₀) = 1 := Subtype.ext h1
    rw [e, map_one]

  have hKo : IsOpen ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) := by
    have e : ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) =
        Subtype.val '' {k : Kw w₀ | χ k = 1} := by
      ext a
      simp [Subgroup.mem_map, MonoidHom.mem_ker]
    rw [e]
    exact (hS.opn w₀ hS.mem).isOpenMap_subtype_val _ hχ
  have hK' := hLO E n S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)) (by
    intro w hw
    by_cases h : w = w₀
    · subst h
      simpa using hKo
    · simpa [Function.update_of_ne h] using hS.opn w hw)
  have hker : IsOpen (((ψ⁻¹).ker : Subgroup (Af E)ˣ) : Set (Af E)ˣ) := by
    refine Subgroup.isOpen_mono (H₁ := (lev S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype))).comap ζ) ?_
      (hK'.preimage hζ.cont)
    intro y hy
    have hy' := mem_lev.1 (Subgroup.mem_comap.1 hy)
    have h0 := hy'.2.1 w₀ hS.mem
    rw [Function.update_self] at h0
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 h0
    have hl : ζ y ∈ lev S Kw := by
      refine mem_lev.2 ⟨hy'.1, fun u hu => ?_, hy'.2.2⟩
      by_cases h : u = w₀
      · subst h
        rw [← hae]
        exact a.2
      · have := hy'.2.1 u hu
        rwa [Function.update_of_ne h] at this
    have h1 : ψ y = 1 := by
      refine B y fun g => A _ hl (by rw [← hae]; exact a.2) ?_ g
      have e : (⟨comp w₀ (ζ y), by rw [← hae]; exact a.2⟩ : Kw w₀) = a := Subtype.ext hae.symm
      rw [e]
      exact ha
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]
  have hprin : ∀ k : Eˣ, (((ψ⁻¹) (diagF E k) : ℂˣ) : ℂ) = (∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ)⁻¹ := by
    intro k
    obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
    have e : ((ψ (diagF E k) : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ := by
      apply cancel
      rw [← hψ, ← hζ.central, h1, hΦ.left, h2]
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e]
  obtain ⟨κ, halg, hloc⟩ := hFH E (ψ⁻¹) (mOf x W j) hker hprin
  refine ⟨κ, halg, ?_, ?_⟩
  · intro w hw y hy
    have h1 : ψ (sgl w y) = 1 := by
      refine B _ fun g => D _ (C _ (hζ.unit w y hy) fun u hu => hζ.off w y u (hw u hu)) ?_ g
      exact hζ.off w y w₀ (hw w₀ hS.mem)
    rw [hloc, MonoidHom.inv_apply, h1, inv_one]
  · intro w hw hnw z hz g
    have hv : κ.val w = (ψ (sgl w (atFin w (unif w))))⁻¹ := by
      show κ.loc w (atFin w (unif w)) = _
      rw [hloc, MonoidHom.inv_apply]
    have hq : ∀ u : Plc E, ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) ≠ 0 := by
      intro u
      have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      exact Nat.cast_ne_zero.2 h0
    have hc : ∀ u, comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) ∈ KGL u n ∧
        (¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1) := by
      intro u
      have hoff : ¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1 := by
        intro h
        rw [map_mul, map_inv, hζ.off w _ u h, (hz u).2 h, inv_one, one_mul]
      refine ⟨?_, hoff⟩
      by_cases h : SameK x (cj u) w
      · obtain ⟨t, ht, hvt⟩ := hζ.unif w _ (unif_spec w) hnw u h
        rw [map_mul, map_inv]
        exact scal_mem_KGL _ _ t _ ht ((hz u).1 h) (hq u) hvt
      · rw [hoff h]
        exact one_mem _
    have hk : (ζ (sgl w (atFin w (unif w))))⁻¹ * z ∈ lev S Kw :=
      C _ (fun u => (hc u).1) fun u hu => (hc u).2 (hw u hu)
    have e : z = ζ (sgl w (atFin w (unif w))) * ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) := by
      rw [mul_inv_cancel_left]
    rw [e, ← mul_assoc, D _ hk ((hc w₀).2 (hw w₀ hS.mem)), hψ, hv]
    simp
