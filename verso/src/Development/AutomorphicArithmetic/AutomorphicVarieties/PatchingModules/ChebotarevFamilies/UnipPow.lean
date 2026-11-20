import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Take `⟨p, hp⟩` from `CharP.exists K`. Use `haveI := hp`. Establish `hpp : p.Prime` using `CharP.char_is_prime K p`. Assume the negation of the conclusion as `hne`. Establish `hpl : p ≠ l` using `fun h => hne (h ▸ hp)`.

Establish `hu : IsUnit (p : ℤ_[l])`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[PadicInt.not_isUnit_iff, ← Int.cast_natCast, PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast]`. Conclude with `hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpp).mp h).symm`. Use `hu.map (algebraMap ℤ_[l] K)` as an intermediate fact.

Rewrite `this` using `[map_natCast, CharP.cast_eq_zero]`. Conclude with `not_isUnit_zero this`.
-/
private theorem charK (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  have hpp : p.Prime := CharP.char_is_prime K p
  by_contra hne
  have hpl : p ≠ l := fun h => hne (h ▸ hp)
  have hu : IsUnit (p : ℤ_[l]) := by
    by_contra h
    rw [PadicInt.not_isUnit_iff, ← Int.cast_natCast, PadicInt.norm_int_lt_one_iff_dvd,
      Int.natCast_dvd_natCast] at h
    exact hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpp).mp h).symm
  have := hu.map (algebraMap ℤ_[l] K)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

/- English proof (translation)
Break down `isEmpty_or_nonempty (Fin n) with hn | hn` into its components or cases. Conclude with `(IsEmpty.false i).elim`. Use `haveI : CharP (PowerSeries K) l := charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l`. Use `set N := M - 1 with hN`. Establish `hMN : M = 1 + N` using `by rw [hN]; abel`.

Establish `hfrob : M ^ l ^ (n * m) - 1 = N ^ l ^ (n * m)`. Rewrite using `[hMN, add_pow_char_pow_of_commute (p := l) (h := Commute.one_left N), one_pow, add_sub_cancel_left]`. Set `f` to `(PowerSeries.constantCoeff : PowerSeries K →+* K).mapMatrix (m := Fin n)`. Establish `hNn : f (N ^ n) = 0`. Rewrite using `[map_pow, hN, map_sub, map_one, RingHom.mapMatrix_apply]`.

Use `Matrix.aeval_self_charpoly (M.map PowerSeries.constantCoeff)` as an intermediate fact. Rewrite `this` using `[hM]`. Simplify `this` using `[map_pow, map_sub]`. Establish `h1 : ∀ a b, (N ^ n) a b ∈ maximalIdeal (PowerSeries K)`. Introduce `a b`.

Establish `h0 : PowerSeries.constantCoeff ((N ^ n) a b) = 0`. Use `congrFun (congrFun hNn a) b` as an intermediate fact. Simplify `this` using `[f, RingHom.mapMatrix_apply]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, h0]`. Conclude with `not_isUnit_zero`.

Establish `hpow : ∀ (I : Ideal (PowerSeries K)) (P : Matrix (Fin n) (Fin n) (PowerSeries K)), (∀ a b, P a b ∈ I) → ∀ k : ℕ, ∀ a b, (P ^ k) a b ∈ I ^ k`. Introduce `I P hP k`. Proceed by induction on `k with`. Consider the case `zero => intro a b`. Simplify using `[Ideal.one_eq_top]`.

Consider the case `succ k ih`. Introduce `a b`. Rewrite using `[pow_succ P, Matrix.mul_apply, pow_succ I]`. Conclude with `Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hP c b)`. Establish `hle : n * m ≤ l ^ (n * m)` using `(Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le`.

Rewrite using `[hfrob, show l ^ (n * m) = n * m + (l ^ (n * m) - n * m) by omega, pow_add, pow_mul, Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hpow _ _ h1 m i c)`.
-/
private theorem unip_pow (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [CharP K l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hM : (M.map (PowerSeries.constantCoeff : PowerSeries K →+* K)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n * m) - 1) i j ∈ maximalIdeal (PowerSeries K) ^ m := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact (IsEmpty.false i).elim
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set N := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  have hfrob : M ^ l ^ (n * m) - 1 = N ^ l ^ (n * m) := by
    rw [hMN, add_pow_char_pow_of_commute (p := l) (h := Commute.one_left N), one_pow, add_sub_cancel_left]
  let f := (PowerSeries.constantCoeff : PowerSeries K →+* K).mapMatrix (m := Fin n)
  have hNn : f (N ^ n) = 0 := by
    rw [map_pow, hN, map_sub, map_one, RingHom.mapMatrix_apply]
    have := Matrix.aeval_self_charpoly (M.map PowerSeries.constantCoeff)
    rw [hM] at this
    simpa [map_pow, map_sub] using this
  have h1 : ∀ a b, (N ^ n) a b ∈ maximalIdeal (PowerSeries K) := by
    intro a b
    have h0 : PowerSeries.constantCoeff ((N ^ n) a b) = 0 := by
      have := congrFun (congrFun hNn a) b
      simpa [f, RingHom.mapMatrix_apply] using this
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, h0]
    exact not_isUnit_zero
  have hpow : ∀ (I : Ideal (PowerSeries K)) (P : Matrix (Fin n) (Fin n) (PowerSeries K)),
      (∀ a b, P a b ∈ I) → ∀ k : ℕ, ∀ a b, (P ^ k) a b ∈ I ^ k := by
    intro I P hP k
    induction k with
    | zero => intro a b; simp [Ideal.one_eq_top]
    | succ k ih =>
      intro a b
      rw [pow_succ P, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hP c b)
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [hfrob, show l ^ (n * m) = n * m + (l ^ (n * m) - n * m) by omega, pow_add, pow_mul,
    Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hpow _ _ h1 m i c)

/- English proof (translation)
Introduce `l _ F n x H hH g hg`. Use `haveI : CharP x.K l := charK l x.K`. Establish `key : ∀ m : ℕ, ∀ i j, (mat x.ρ g - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m`. Introduce `m`. Set `φ : F.G₀ →* Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)` to `(Ideal.Quotient.mk (maximalIdeal (PowerSeries x.K) ^ m)).mapMatrix.toMonoidHom.comp (mat x.ρ)`.

Establish `hφ : ∀ y, φ y = 1 ↔ ∀ i j, (mat x.ρ y - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m`. Introduce `y`. Rewrite using `[← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, ← Ideal.Quotient.eq]`.

Use `show Ideal.Quotient.mk _ (mat x.ρ y i j) = (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j ↔ _`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Set `T : Subgroup F.Γ` to `φ.ker.map F.η.ker.subtype`. Establish `hTopen : IsOpen (T : Set F.Γ)`.

Establish `hK : IsOpen (φ.ker : Set F.G₀)`. Establish `e : (φ.ker : Set F.G₀) = ⋂ i, ⋂ j, {y : F.G₀ | φ y i j = (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j}`. Use extensionality with `y`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `Matrix.ext_iff.symm`.

Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (x.cont i j m : IsLocallyConstant fun y : F.G₀ => φ y i j).isOpen_fiber _`. Rewrite using `[Subgroup.coe_map]`. Conclude with `F.η_open.isOpenMap_subtype_val _ hK`. Take `⟨V, hV⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hTopen T.one_mem`.

Set `W : OpenNormalSubgroup F.Γ` to `{ toSubgroup := T.normalCore isOpen' := Subgroup.isOpen_mono (H₁ := V.toSubgroup) (Subgroup.normal_le_normalCore.mpr fun a ha => hV ha) V.toOpenSubgroup.isOpen isNormal' := Subgroup.normalCore_normal T }`. Establish `hW : ∀ h ∈ H.toSubgroup, ∃ e, h ^ l ^ e ∈ W`. Introduce `h hh`. Use `⟨n * m, ?_⟩` and prove the remaining obligations. Use `show ∀ b : F.Γ, b * h ^ l ^ (n * m) * b⁻¹ ∈ T`.

Introduce `b`. Rewrite using `[← conj_pow]`. Establish `hbh : b * h * b⁻¹ ∈ H.toSubgroup` using `H.isNormal'.conj_mem h hh b`. Take `⟨he, hchar⟩` from `hH _ hbh`. Use `Subgroup.mem_map.mpr ⟨⟨b * h * b⁻¹, he⟩ ^ l ^ (n * m), ?_, by simp⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.mem_ker, hφ, map_pow]`. Conclude with `unip_pow l x.K n m _ hchar`. Establish `hgW : (g : F.Γ) ∈ T.normalCore`. Establish `h2` using `hg`. Simplify using `only [UpperTheory.V.Pa.PL, Subgroup.mem_iInf] at h2`.

Conclude with `h2 W hW`. Establish `h1` using `T.normalCore_le hgW`. Take `⟨y, hy, hyg⟩` from `Subgroup.mem_map.mp h1`. Establish `hyg' : y = g` using `Subtype.ext hyg`. Rewrite using `[← hyg']`.

Conclude with `(hφ y).mp hy`. Apply `Units.ext` to reduce the goal to its premises. Use `show mat x.ρ g = 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `h0 : (mat x.ρ g - 1) i j ∈ ⨅ m, maximalIdeal (PowerSeries x.K) ^ m` using `Submodule.mem_iInf _ |>.mpr fun m => key m i j`.

Rewrite `h0` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top, Ideal.mem_bot, Matrix.sub_apply, sub_eq_zero]`. Conclude with `h0`.
-/
theorem UpperTheory.V.Pa.rhoPL :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : OpenNormalSubgroup F.Γ), (∀ g ∈ H, ∃ h : F.η g = 1, ((mat x.ρ ⟨g, h⟩).map (PowerSeries.constantCoeff : x.A →+* x.K)).charpoly = (Polynomial.X - 1) ^ n) → ∀ g : F.G₀, (g : F.Γ) ∈ PL l H.toSubgroup → x.ρ g = 1 := by
  intro l _ F n x H hH g hg
  haveI : CharP x.K l := charK l x.K
  have key : ∀ m : ℕ, ∀ i j, (mat x.ρ g - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
    intro m
    let φ : F.G₀ →* Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m) :=
      (Ideal.Quotient.mk (maximalIdeal (PowerSeries x.K) ^ m)).mapMatrix.toMonoidHom.comp (mat x.ρ)
    have hφ : ∀ y, φ y = 1 ↔ ∀ i j, (mat x.ρ y - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
      intro y
      rw [← Matrix.ext_iff]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
      show Ideal.Quotient.mk _ (mat x.ρ y i j) =
          (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j ↔ _
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    let T : Subgroup F.Γ := φ.ker.map F.η.ker.subtype
    have hTopen : IsOpen (T : Set F.Γ) := by
      have hK : IsOpen (φ.ker : Set F.G₀) := by
        have e : (φ.ker : Set F.G₀) = ⋂ i, ⋂ j, {y : F.G₀ | φ y i j =
            (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j} := by
          ext y
          simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
          exact Matrix.ext_iff.symm
        rw [e]
        exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
          (x.cont i j m : IsLocallyConstant fun y : F.G₀ => φ y i j).isOpen_fiber _
      rw [Subgroup.coe_map]
      exact F.η_open.isOpenMap_subtype_val _ hK
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hTopen T.one_mem
    let W : OpenNormalSubgroup F.Γ :=
      { toSubgroup := T.normalCore
        isOpen' := Subgroup.isOpen_mono (H₁ := V.toSubgroup)
          (Subgroup.normal_le_normalCore.mpr fun a ha => hV ha) V.toOpenSubgroup.isOpen
        isNormal' := Subgroup.normalCore_normal T }
    have hW : ∀ h ∈ H.toSubgroup, ∃ e, h ^ l ^ e ∈ W := by
      intro h hh
      refine ⟨n * m, ?_⟩
      show ∀ b : F.Γ, b * h ^ l ^ (n * m) * b⁻¹ ∈ T
      intro b
      rw [← conj_pow]
      have hbh : b * h * b⁻¹ ∈ H.toSubgroup := H.isNormal'.conj_mem h hh b
      obtain ⟨he, hchar⟩ := hH _ hbh
      refine Subgroup.mem_map.mpr ⟨⟨b * h * b⁻¹, he⟩ ^ l ^ (n * m), ?_, by simp⟩
      rw [MonoidHom.mem_ker, hφ, map_pow]
      exact unip_pow l x.K n m _ hchar
    have hgW : (g : F.Γ) ∈ T.normalCore := by
      have h2 := hg
      simp only [UpperTheory.V.Pa.PL, Subgroup.mem_iInf] at h2
      exact h2 W hW
    have h1 := T.normalCore_le hgW
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp h1
    have hyg' : y = g := Subtype.ext hyg
    rw [← hyg']
    exact (hφ y).mp hy
  apply Units.ext
  show mat x.ρ g = 1
  refine Matrix.ext fun i j => ?_
  have h0 : (mat x.ρ g - 1) i j ∈ ⨅ m, maximalIdeal (PowerSeries x.K) ^ m :=
    Submodule.mem_iInf _ |>.mpr fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot, Matrix.sub_apply, sub_eq_zero] at h0
  exact h0
