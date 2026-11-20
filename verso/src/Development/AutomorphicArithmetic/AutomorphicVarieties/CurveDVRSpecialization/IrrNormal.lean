import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CharPerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CliffPrime
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtIntegral

open Matrix Polynomial UpperTheory.V.U3 UpperTheory.V.Alg

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qe16.ext_integral hinj φ`.
-/
private theorem ext_integral {B S K : Type} [CommRing B] [CommRing S] [Field K] [IsAlgClosed K] [Algebra B S]
    [Algebra.IsIntegral B S] (hinj : Function.Injective (algebraMap B S)) (φ : B →+* K) :
    ∃ Φ : S →+* K, ∀ b, Φ (algebraMap B S b) = φ b :=
  _root_.UpperTheory.Reformulated.B.Qe16.ext_integral hinj φ

/- English proof (translation)
Rewrite using `[← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_diagonal]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.toLin'_apply, h, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij, Finsupp.single_apply, Ne.symm hij]`.
-/
private theorem charpoly_of_basis {κ : Type} [Field κ] {n : ℕ} (M : Matrix (Fin n) (Fin n) κ)
    (b : Module.Basis (Fin n) κ (Fin n → κ)) (a : Fin n → κ) (h : ∀ i, M *ᵥ b i = a i • b i) :
    M.charpoly = ∏ i, (X - C (a i)) := by
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, h, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Finsupp.single_apply, Ne.symm hij]

/- English proof (translation)
Use `letI : Algebra B κ := j.toAlgebra`. Establish `hinj : Function.Injective (algebraMap B (integralClosure B κ))`. Introduce `x y hxy`. Conclude with `hj (congrArg Subtype.val hxy)`. Take `⟨Φ, hΦ⟩` from `ext_integral hinj ((algebraMap k (AlgebraicClosure k)).comp φ)`.

Use `⟨(integralClosure B κ).toSubring, Φ, fun n p a hp => ?_⟩` and prove the remaining obligations. Establish `hm : p.Monic`. Apply `Polynomial.monic_of_injective hj` to reduce the goal to its premises. Rewrite using `[hp]`. Conclude with `monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _`.

Establish `h : ∀ i, a i ∈ integralClosure B κ` using `fun i => by`. Use `⟨p, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_eq_eval_map]`. Express the relevant statement in the definitionally equal form `(p.map j).eval _ = 0`. Rewrite using `[hp, eval_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `h1 : p.map (algebraMap B (integralClosure B κ)) = ∏ i, (X - C (⟨a i, h i⟩ : integralClosure B κ))`. Apply `Polynomial.map_injective (integralClosure B κ).val.toRingHom Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.map_map, Polynomial.map_prod]`.

Simplify using `only [Polynomial.map_sub, map_X, map_C]`. Conclude with `hp`. Establish `h2` using `congrArg (Polynomial.map Φ) h1`. Rewrite `h2` using `[Polynomial.map_map, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, map_X, map_C] at h2`.

Rewrite using `[Polynomial.map_map]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Use `congr 1`. Conclude with `RingHom.ext fun b => (hΦ b).symm`.
-/
private theorem reduce_roots {κ k B : Type} [Field κ] [Field k] [CommRing B] (j : B →+* κ)
    (hj : Function.Injective j) (φ : B →+* k) :
    ∃ (S : Subring κ) (Φ : S →+* AlgebraicClosure k), ∀ (n : ℕ) (p : B[X]) (a : Fin n → κ),
      p.map j = ∏ i, (X - C (a i)) → ∃ h : ∀ i, a i ∈ S,
        (p.map φ).map (algebraMap k (AlgebraicClosure k)) = ∏ i, (X - C (Φ ⟨a i, h i⟩)) := by
  letI : Algebra B κ := j.toAlgebra
  have hinj : Function.Injective (algebraMap B (integralClosure B κ)) := by
    intro x y hxy
    exact hj (congrArg Subtype.val hxy)
  obtain ⟨Φ, hΦ⟩ := ext_integral hinj ((algebraMap k (AlgebraicClosure k)).comp φ)
  refine ⟨(integralClosure B κ).toSubring, Φ, fun n p a hp => ?_⟩
  have hm : p.Monic := by
    apply Polynomial.monic_of_injective hj
    rw [hp]
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have h : ∀ i, a i ∈ integralClosure B κ := fun i => by
    refine ⟨p, hm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map]
    change (p.map j).eval _ = 0
    rw [hp, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine ⟨h, ?_⟩
  have h1 : p.map (algebraMap B (integralClosure B κ)) = ∏ i, (X - C (⟨a i, h i⟩ : integralClosure B κ)) := by
    apply Polynomial.map_injective (integralClosure B κ).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    exact hp
  have h2 := congrArg (Polynomial.map Φ) h1
  rw [Polynomial.map_map, Polynomial.map_prod] at h2
  simp only [Polynomial.map_sub, map_X, map_C] at h2
  rw [Polynomial.map_map]
  refine Eq.trans ?_ h2
  congr 1
  exact RingHom.ext fun b => (hΦ b).symm

/- English proof (translation)
Introduce `G κ k B _ _ _ _ _ n hn r hr j φ χ hj hred D _ ι ψ hψ U _ hdist hχ`. Break down `UpperTheory.V.Pr.cliffPrime G κ n hn r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Establish `h2` using `hn.two_le`.

Take `⟨g, hg, hne⟩` from `hdist ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)`. Take `⟨c, hc⟩` from `h _ hg`. Establish `hall : ∀ a, ((ψ a g : κˣ) : κ) = c` using `fun a => by`. Establish `h1` using `hψ g`. Rewrite `h1` using `[hc, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]`.

Establish `h3` using `congrArg (Polynomial.eval ((ψ a g : κˣ) : κ)) h1`. Rewrite `h3` using `[UpperTheory.V.Pr.chPoly, eval_prod, eval_prod, Finset.prod_eq_zero (f := fun i => eval ((ψ a g : κˣ) : κ) (X - C ((ψ i g : κˣ) : κ))) (Finset.mem_univ a) (by simp), Finset.prod_eq_zero_iff]`. Take `⟨_, _, h4⟩` from `h3`. Simplify `h4` using `[sub_eq_zero]`. Conclude with `hne (Units.ext ((hall _).trans (hall _).symm))`.

It suffices to derive a contradiction. Use `choose c hc using hπ`. Establish `hb : ∀ i (x y : κ), x • b i = y • b i → x = y` using `fun i x y h => smul_left_injective κ (b.ne_zero i) h`. Establish `c1 : ∀ i, c 1 i = 1` using `fun i => by`. Use `hc 1 i` as an intermediate fact.

Simplify using `only [UpperTheory.V.Pr.gm, map_one, Units.val_one, Matrix.one_mulVec, Equiv.Perm.coe_one, id] at this`. Conclude with `hb i _ _ (by rw [← this, one_smul])`. Establish `cmul : ∀ g h i, c (g * h) i = c g (π h i) * c h i` using `fun g h i => by`. Use `hc (g * h) i` as an intermediate fact. Simplify using `only [UpperTheory.V.Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at this`.

Rewrite `this` using `[hc h i, Matrix.mulVec_smul, hc g, smul_smul]`. Rewrite using `[mul_comm]`. Conclude with `(hb _ _ _ this).symm`. Establish `cne : ∀ g i, c g i ≠ 0` using `fun g i h0 => by`. Use `cmul g⁻¹ g i` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel, c1, h0, mul_zero]`. Conclude with `one_ne_zero this`. Establish `cconj : ∀ g h i, π h = 1 → c (g * h * g⁻¹) (π g i) = c h i` using `fun g h i hh => by`. Establish `e1` using `cmul (g * h * g⁻¹) g i`. Rewrite `e1` using `[inv_mul_cancel_right, cmul, hh]`.

Apply `mul_right_cancel₀ (cne g i)` to reduce the goal to its premises. Rewrite using `[← e1, mul_comm]`. Both sides reduce to the same expression. Establish `hU : ∀ u ∈ U, π u = 1` using `fun u hu => by`. Use extensionality with `i`.

Assume the negation of the conclusion as `hne`. Establish `e` using `(hla i ⟨u, hu⟩).symm.trans (hc u i)`. Establish `e2` using `congrArg (fun v => b.repr v (π u i)) e`. Establish `hne' : i ≠ π u i` using `fun h => hne (by rw [← h]; rfl)`. Simplify using `[Finsupp.single_apply, hne'] at e2`.

Conclude with `cne u i e2.symm`. Set `kap : Fin n → π.ker →* κ` to `fun i => { toFun := fun h => c h i map_one' := c1 i map_mul' := fun g h => by`. Use `cmul g h i` as an intermediate fact. Rewrite `this` using `[(MonoidHom.mem_ker.1 h.2)]`. Conclude with `this }`.

Establish `hchar : ∀ h, π h = 1 → (UpperTheory.V.Pr.gm r h).charpoly = ∏ i, (X - C (c h i))` using `fun h hh => charpoly_of_basis _ b _ fun i => by rw [hc, hh]; rfl`. Establish `hD : ∀ d, π (ι d) = 1`. Set `e : U.comap ι →* π.ker` to `(ι.comp (U.comap ι).subtype).codRestrict π.ker fun u => hU _ u.2`. Take `⟨σ, hσ⟩` from `UpperTheory.V.Pr.charPerm (U.comap ι) κ n (fun i => (ψ i).comp (U.comap ι).subtype) (fun i => ((kap i).comp e).toHomUnits) (fun u => by`. Use `hψ u` as an intermediate fact.

Rewrite `this` using `[hchar _ (hU _ u.2)]`. Conclude with `this.symm)`. Establish `hσ' : ∀ i u, ι u ∈ U → c (ι u) i = (ψ (σ i) u : κˣ)` using `fun i u hu => by`. Use `congrArg Units.val (DFunLike.congr_fun (hσ i) (⟨u, hu⟩ : U.comap ι))` as an intermediate fact. Conclude with `this`.

Introduce `d`. Use `Equiv.ext fun i => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨u, hu, hne'⟩` from `hdist (σ (π (ι d) i)) (σ i) (fun h => hne (σ.injective h))`. Apply `hne'` to reduce the goal to its premises.

Establish `e1` using `cconj (ι d) (ι u) i (hU _ hu)`. Establish `hu' : ι (d * u * d⁻¹) ∈ U`. Rewrite using `[map_mul, map_mul, map_inv]`. Conclude with `Subgroup.Normal.conj_mem ‹_› _ hu _`. Rewrite `e1` using `[← map_inv, ← map_mul, ← map_mul, hσ' _ _ hu', hσ' _ _ hu, map_mul, map_mul, map_inv, mul_inv_cancel_comm]`.

Conclude with `Units.ext e1`. Take `⟨S, Φ, hS⟩` from `reduce_roots j hj φ`. Set `t : kˣ →* (AlgebraicClosure k)ˣ` to `Units.map (algebraMap k (AlgebraicClosure k)).toMonoidHom`. Establish `ht : Function.Injective t` using `Units.map_injective (algebraMap k (AlgebraicClosure k)).injective`. Establish `key : ∀ h, π h = 1 → ∃ hh : ∀ i, c h i ∈ S, UpperTheory.V.Pr.chPoly (fun i => t.comp (χ i)) h = ∏ i, (X - C (Φ ⟨c h i, hh i⟩))` using `fun h hh => by`.

Take `⟨p, hp1, hp2⟩` from `hred h`. Take `⟨hm, hq⟩` from `hS n p _ (hp1.trans (hchar h hh))`. Use `⟨hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← hq, hp2, UpperTheory.V.Pr.chPoly, UpperTheory.V.Pr.chPoly, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, map_X, map_C]`.

Both sides reduce to the same expression. Use `choose hmem hkey using key`. Set `kb : Fin n → π.ker →* AlgebraicClosure k` to `fun i => Φ.toMonoidHom.comp ((kap i).codRestrict S fun h => hmem h h.2 i)`. Take `⟨τ, hτ⟩` from `UpperTheory.V.Pr.charPerm π.ker (AlgebraicClosure k) n (fun i => (t.comp (χ i)).comp π.ker.subtype) (fun i => (kb i).toHomUnits) (fun h => hkey h h.2)`. Establish `hτ' : ∀ i h (hh : π h = 1), Φ ⟨c h i, hmem h hh i⟩ = (t (χ (τ i) h) : (AlgebraicClosure k)ˣ)` using `fun i h hh => by`.

Use `congrArg Units.val (DFunLike.congr_fun (hτ i) (⟨h, hh⟩ : π.ker))` as an intermediate fact. Conclude with `this`. Take `⟨a, a', d, hne⟩` from `hχ`. Take `⟨g, hg⟩` from `htr (τ.symm a') (τ.symm a)`. Apply `hne` to reduce the goal to its premises.

Apply `ht` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Establish `hc' : π (g * ι d * g⁻¹) = 1` using `by rw [map_mul, map_mul, hD, mul_one, map_inv, mul_inv_cancel]`. Establish `e1` using `hτ' (τ.symm a) _ hc'`. Establish `e2` using `hτ' (τ.symm a') _ (hD d)`.

Rewrite `e1`, `e2` using `[Equiv.apply_symm_apply]`. Rewrite `e1` using `[map_mul (χ a), map_mul (χ a), map_inv (χ a), mul_inv_cancel_comm]`. Rewrite using `[← e1, ← e2]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show c _ _ = c _ _`. Rewrite using `[← hg]`. Conclude with `cconj _ _ _ (hD d)`.
-/
theorem UpperTheory.V.Pr.irrNormal :
    UpperTheory.V.Pr.IrrNormal := by
  intro G κ k B _ _ _ _ _ n hn r hr j φ χ hj hred D _ ι ψ hψ U _ hdist hχ
  rcases UpperTheory.V.Pr.cliffPrime G κ n hn r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
  · exact h
  · exfalso
    have h2 := hn.two_le
    obtain ⟨g, hg, hne⟩ := hdist ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
    obtain ⟨c, hc⟩ := h _ hg
    have hall : ∀ a, ((ψ a g : κˣ) : κ) = c := fun a => by
      have h1 := hψ g
      rw [hc, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal] at h1
      have h3 := congrArg (Polynomial.eval ((ψ a g : κˣ) : κ)) h1
      rw [UpperTheory.V.Pr.chPoly, eval_prod, eval_prod,
        Finset.prod_eq_zero (f := fun i => eval ((ψ a g : κˣ) : κ) (X - C ((ψ i g : κˣ) : κ)))
          (Finset.mem_univ a) (by simp), Finset.prod_eq_zero_iff] at h3
      obtain ⟨_, _, h4⟩ := h3
      simpa [sub_eq_zero] using h4
    exact hne (Units.ext ((hall _).trans (hall _).symm))
  exfalso
  choose c hc using hπ
  have hb : ∀ i (x y : κ), x • b i = y • b i → x = y := fun i x y h =>
    smul_left_injective κ (b.ne_zero i) h
  have c1 : ∀ i, c 1 i = 1 := fun i => by
    have := hc 1 i
    simp only [UpperTheory.V.Pr.gm, map_one, Units.val_one, Matrix.one_mulVec, Equiv.Perm.coe_one, id] at this
    exact hb i _ _ (by rw [← this, one_smul])
  have cmul : ∀ g h i, c (g * h) i = c g (π h i) * c h i := fun g h i => by
    have := hc (g * h) i
    simp only [UpperTheory.V.Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at this
    rw [hc h i, Matrix.mulVec_smul, hc g, smul_smul] at this
    rw [mul_comm]
    exact (hb _ _ _ this).symm
  have cne : ∀ g i, c g i ≠ 0 := fun g i h0 => by
    have := cmul g⁻¹ g i
    rw [inv_mul_cancel, c1, h0, mul_zero] at this
    exact one_ne_zero this
  have cconj : ∀ g h i, π h = 1 → c (g * h * g⁻¹) (π g i) = c h i := fun g h i hh => by
    have e1 := cmul (g * h * g⁻¹) g i
    rw [inv_mul_cancel_right, cmul, hh] at e1
    apply mul_right_cancel₀ (cne g i)
    rw [← e1, mul_comm]; rfl
  have hU : ∀ u ∈ U, π u = 1 := fun u hu => by
    ext i
    by_contra hne
    have e := (hla i ⟨u, hu⟩).symm.trans (hc u i)
    have e2 := congrArg (fun v => b.repr v (π u i)) e
    have hne' : i ≠ π u i := fun h => hne (by rw [← h]; rfl)
    simp [Finsupp.single_apply, hne'] at e2
    exact cne u i e2.symm
  let kap : Fin n → π.ker →* κ := fun i =>
    { toFun := fun h => c h i
      map_one' := c1 i
      map_mul' := fun g h => by
        have := cmul g h i
        rw [(MonoidHom.mem_ker.1 h.2)] at this
        exact this }
  have hchar : ∀ h, π h = 1 → (UpperTheory.V.Pr.gm r h).charpoly = ∏ i, (X - C (c h i)) := fun h hh =>
    charpoly_of_basis _ b _ fun i => by rw [hc, hh]; rfl

  have hD : ∀ d, π (ι d) = 1 := by
    let e : U.comap ι →* π.ker :=
      (ι.comp (U.comap ι).subtype).codRestrict π.ker fun u => hU _ u.2
    obtain ⟨σ, hσ⟩ := UpperTheory.V.Pr.charPerm (U.comap ι) κ n (fun i => (ψ i).comp (U.comap ι).subtype)
      (fun i => ((kap i).comp e).toHomUnits) (fun u => by
        have := hψ u
        rw [hchar _ (hU _ u.2)] at this
        exact this.symm)
    have hσ' : ∀ i u, ι u ∈ U → c (ι u) i = (ψ (σ i) u : κˣ) := fun i u hu => by
      have := congrArg Units.val (DFunLike.congr_fun (hσ i) (⟨u, hu⟩ : U.comap ι))
      exact this
    intro d
    refine Equiv.ext fun i => ?_
    by_contra hne
    obtain ⟨u, hu, hne'⟩ := hdist (σ (π (ι d) i)) (σ i) (fun h => hne (σ.injective h))
    apply hne'
    have e1 := cconj (ι d) (ι u) i (hU _ hu)
    have hu' : ι (d * u * d⁻¹) ∈ U := by
      rw [map_mul, map_mul, map_inv]; exact Subgroup.Normal.conj_mem ‹_› _ hu _
    rw [← map_inv, ← map_mul, ← map_mul, hσ' _ _ hu', hσ' _ _ hu, map_mul, map_mul, map_inv,
      mul_inv_cancel_comm] at e1
    exact Units.ext e1
  obtain ⟨S, Φ, hS⟩ := reduce_roots j hj φ
  let t : kˣ →* (AlgebraicClosure k)ˣ := Units.map (algebraMap k (AlgebraicClosure k)).toMonoidHom
  have ht : Function.Injective t := Units.map_injective (algebraMap k (AlgebraicClosure k)).injective
  have key : ∀ h, π h = 1 → ∃ hh : ∀ i, c h i ∈ S,
      UpperTheory.V.Pr.chPoly (fun i => t.comp (χ i)) h = ∏ i, (X - C (Φ ⟨c h i, hh i⟩)) := fun h hh => by
    obtain ⟨p, hp1, hp2⟩ := hred h
    obtain ⟨hm, hq⟩ := hS n p _ (hp1.trans (hchar h hh))
    refine ⟨hm, ?_⟩
    rw [← hq, hp2, UpperTheory.V.Pr.chPoly, UpperTheory.V.Pr.chPoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    rfl
  choose hmem hkey using key
  let kb : Fin n → π.ker →* AlgebraicClosure k := fun i =>
    Φ.toMonoidHom.comp ((kap i).codRestrict S fun h => hmem h h.2 i)
  obtain ⟨τ, hτ⟩ := UpperTheory.V.Pr.charPerm π.ker (AlgebraicClosure k) n
    (fun i => (t.comp (χ i)).comp π.ker.subtype) (fun i => (kb i).toHomUnits) (fun h => hkey h h.2)
  have hτ' : ∀ i h (hh : π h = 1), Φ ⟨c h i, hmem h hh i⟩ = (t (χ (τ i) h) : (AlgebraicClosure k)ˣ) :=
    fun i h hh => by
      have := congrArg Units.val (DFunLike.congr_fun (hτ i) (⟨h, hh⟩ : π.ker))
      exact this
  obtain ⟨a, a', d, hne⟩ := hχ
  obtain ⟨g, hg⟩ := htr (τ.symm a') (τ.symm a)
  apply hne
  apply ht
  apply Units.ext
  have hc' : π (g * ι d * g⁻¹) = 1 := by rw [map_mul, map_mul, hD, mul_one, map_inv, mul_inv_cancel]
  have e1 := hτ' (τ.symm a) _ hc'
  have e2 := hτ' (τ.symm a') _ (hD d)
  rw [Equiv.apply_symm_apply] at e1 e2
  rw [map_mul (χ a), map_mul (χ a), map_inv (χ a), mul_inv_cancel_comm] at e1
  rw [← e1, ← e2]
  congr 1
  apply Subtype.ext
  show c _ _ = c _ _
  rw [← hg]
  exact cconj _ _ _ (hD d)
