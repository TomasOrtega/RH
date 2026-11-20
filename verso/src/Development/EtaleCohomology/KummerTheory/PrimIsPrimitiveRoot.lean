import Development.EtaleCohomology.KummerTheory.OneExPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory

/- English proof (translation)
Establish `h` using `(toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality f.op`. Establish `h2` using `LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))`. Simplify using `only [ModuleCat.hom_comp] at h2`. Unfold `twGen ofRings.sec`. Rewrite using `[← Finsupp.mapDomain_single]`.

Conclude with `h2.symm`.
-/
theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (f : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res f (twGen i ζ) = twGen i (Prim.map f.appTop.hom ζ) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality f.op
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))
  simp only [ModuleCat.hom_comp] at h2
  unfold twGen ofRings.sec
  rw [← Finsupp.mapDomain_single]
  exact h2.symm

/- English proof (translation)
Unfold `twGen`. Use `congr 1`. Use `(Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)` and prove the remaining obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem twGen_zero_eq {q : ℕ} {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

/- English proof (translation)
Take `⟨c, hc⟩` from `cyclotomic.dvd_X_pow_sub_one q ℤ`. Establish `h` using `congrArg (aeval ζ.1) hc`. Rewrite `h` using `[map_mul, ζ.2.2, zero_mul]`. Simplify `h` using `[sub_eq_zero]`.
-/
theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨c, hc⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

/- English proof (translation)
Take `⟨z, hz1, hz2⟩` from `μ`. Establish `: NeZero (q : K)` using `⟨hz1.ne_zero⟩`. Use `(isRoot_cyclotomic_iff).1 ?_` and prove the remaining obligations. Rewrite `hz2` using `[aeval_def, algebraMap_int_eq]`. Use `show Polynomial.eval z (cyclotomic q K) = 0`.

Rewrite using `[← map_cyclotomic_int, Polynomial.eval_map]`. Conclude with `hz2`.
-/
theorem prim_isPrimitiveRoot {q : ℕ} {K : Type} [Field K] (μ : Prim q K) : IsPrimitiveRoot μ.1 q := by
  obtain ⟨z, hz1, hz2⟩ := μ
  have : NeZero (q : K) := ⟨hz1.ne_zero⟩
  refine (isRoot_cyclotomic_iff).1 ?_
  rw [aeval_def, algebraMap_int_eq] at hz2
  show Polynomial.eval z (cyclotomic q K) = 0
  rw [← map_cyclotomic_int, Polynomial.eval_map]
  exact hz2

/- English proof (translation)
Set `e` to `(U.evaluation ⊤ x trivial).hom`. Establish `hζ` using `prim_isPrimitiveRoot (Prim.map e ζ)`. Establish `hξ` using `prim_isPrimitiveRoot (Prim.map e ξ)`. Take `⟨i, hi, hie⟩` from `hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one`. Establish `hcop : i.Coprime q` using `(hζ.pow_iff_coprime (NeZero.pos q) i).1 (hie ▸ hξ)`.

Establish `hav : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i`. Simplify using `[ZMod.val_natCast, Nat.mod_eq_of_lt hi]`. Take `⟨k, hk⟩` from `binomExpansion ((X : Polynomial Γ(U, ⊤)) ^ q - 1) ξ.1 (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1)`. Establish `hξq` using `prim_pow ξ`. Establish `hζq : (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val) ^ q = 1`.

Rewrite using `[← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]`. Use `⟨(q : Γ(U, ⊤)) * ξ.1 ^ (q - 1) + k * (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1), ZMod.unitOfCoprime i hcop, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x (show x ∈ (⊤ : U.Opens) from trivial)]`. Establish `hy : e (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) = 0`. Rewrite using `[map_sub, map_pow, hav, sub_eq_zero]`.

Conclude with `hie`. Establish `hq : ((q : ℕ) : U.residueField x) ≠ 0` using `(Prim.map e ξ).2.1.ne_zero`. Express the relevant statement in the definitionally equal form `e _ ≠ 0`. Rewrite using `[map_add, map_mul, map_mul, hy, mul_zero, add_zero, map_pow, map_natCast]`. Conclude with `mul_ne_zero hq (pow_ne_zero _ (hξ.ne_zero (NeZero.ne q)))`.

Establish `hs : ξ.1 + (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) = ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val` using `by ring`. Rewrite `hk` using `[hs]`. Simplify using `only [eval_sub, eval_pow, eval_X, eval_one, hζq, hξq, sub_self, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_C] at hk`. Take the linear combination `hk`.
-/
theorem local_pow {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (x : U) :
    ∃ (h : Γ(U, ⊤)) (a : (ZMod q)ˣ), x ∈ U.basicOpen h ∧ h * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0 := by
  let e := (U.evaluation ⊤ x trivial).hom
  have hζ := prim_isPrimitiveRoot (Prim.map e ζ)
  have hξ := prim_isPrimitiveRoot (Prim.map e ξ)
  obtain ⟨i, hi, hie⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hcop : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (hie ▸ hξ)
  have hav : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  obtain ⟨k, hk⟩ := binomExpansion ((X : Polynomial Γ(U, ⊤)) ^ q - 1) ξ.1
    (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1)
  have hξq := prim_pow ξ
  have hζq : (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, prim_pow ζ, one_pow]
  refine ⟨(q : Γ(U, ⊤)) * ξ.1 ^ (q - 1) + k * (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1),
    ZMod.unitOfCoprime i hcop, ?_, ?_⟩
  · rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x (show x ∈ (⊤ : U.Opens) from trivial)]
    have hy : e (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) = 0 := by
      rw [map_sub, map_pow, hav, sub_eq_zero]
      exact hie
    have hq : ((q : ℕ) : U.residueField x) ≠ 0 := (Prim.map e ξ).2.1.ne_zero
    change e _ ≠ 0
    rw [map_add, map_mul, map_mul, hy, mul_zero, add_zero, map_pow, map_natCast]
    exact mul_ne_zero hq (pow_ne_zero _ (hξ.ne_zero (NeZero.ne q)))
  · have hs : ξ.1 + (ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val - ξ.1) =
        ζ.1 ^ ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val := by ring
    rw [hs] at hk
    simp only [eval_sub, eval_pow, eval_X, eval_one, hζq, hξq, sub_self, derivative_sub, derivative_X_pow,
      derivative_one, sub_zero, eval_mul, eval_C] at hk
    linear_combination hk

/- English proof (translation)
Set `S : Sieve U` to `{ arrows := fun W f => Sec.res f s = Sec.res f t downward_closed := by`. Introduce `W W' f hf g`. Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hf ⊢`. Rewrite using `[hf] }`. Establish `hS : S ∈ Scheme.etaleTopology U`.

Apply `Scheme.zariskiTopology_le_etaleTopology` to reduce the goal to its premises. Use `Scheme.zariskiTopology.superset_covering ?_ (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover V hV))` and prove the remaining obligations. Rewrite using `[Sieve.ofArrows, Sieve.generate_le_iff]`. Introduce and unpack `W f ⟨i⟩`. Conclude with `h i`.

Establish `hsh : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _)` using `(isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.cond)`. Conclude with `(hsh S hS).isSeparatedFor.ext fun W f hf => hf`.
-/
theorem sec_eq_of_cover {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} {ι : Type} (V : ι → U.Opens)
    (hV : TopologicalSpace.IsOpenCover V) (s t : Sec F U) (h : ∀ i, Sec.res (V i).ι s = Sec.res (V i).ι t) :
    s = t := by
  let S : Sieve U := {
    arrows := fun W f => Sec.res f s = Sec.res f t
    downward_closed := by
      intro W W' f hf g
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hf ⊢
      rw [hf] }
  have hS : S ∈ Scheme.etaleTopology U := by
    apply Scheme.zariskiTopology_le_etaleTopology
    refine Scheme.zariskiTopology.superset_covering ?_
      (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover V hV))
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W f ⟨i⟩
    exact h i
  have hsh : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.cond)
  exact (hsh S hS).isSeparatedFor.ext fun W f hf => hf

/- English proof (translation)
Use `choose h a hx hh using fun x : U => local_pow ζ ξ x`. Use `sec_eq_of_cover (fun x => U.basicOpen (h x)) ?_ _ _ fun x => ?_` and prove the remaining obligations. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨y, hx y⟩`. Rewrite using `[twGen_res, twGen_res]`.

Apply `twGen_zero_eq _ _ (a x)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(U.basicOpen (h x)).ι.appTop.hom ξ.1 = (U.basicOpen (h x)).ι.appTop.hom ζ.1 ^ _`. Rewrite using `[← map_pow, ← sub_eq_zero, ← map_sub]`. Establish `hu : IsUnit ((U.basicOpen (h x)).ι.appTop.hom (h x))`. Rewrite using `[Scheme.Opens.ι_appTop]`.

Establish `key : ∀ (W : U.Opens) (hW : W = U.basicOpen (h x)) (hle : W ≤ ⊤), IsUnit (U.presheaf.map (homOfLE hle).op (h x))`. Introduce and unpack `W rfl hle`. Conclude with `RingedSpace.isUnit_res_basicOpen U.toRingedSpace (h x)`. Conclude with `key _ (Scheme.Opens.ι_image_top _) _`. Conclude with `hu.mul_right_eq_zero.1 (by rw [← map_mul, hh x, map_zero])`.
-/
theorem twGen_zero_indep {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) :
    twGen 0 ξ = twGen 0 ζ := by
  choose h a hx hh using fun x : U => local_pow ζ ξ x
  refine sec_eq_of_cover (fun x => U.basicOpen (h x)) ?_ _ _ fun x => ?_
  · refine eq_top_iff.2 fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hx y⟩
  rw [twGen_res, twGen_res]
  apply twGen_zero_eq _ _ (a x)
  change (U.basicOpen (h x)).ι.appTop.hom ξ.1 = (U.basicOpen (h x)).ι.appTop.hom ζ.1 ^ _
  rw [← map_pow, ← sub_eq_zero, ← map_sub]
  have hu : IsUnit ((U.basicOpen (h x)).ι.appTop.hom (h x)) := by
    rw [Scheme.Opens.ι_appTop]
    have key : ∀ (W : U.Opens) (hW : W = U.basicOpen (h x)) (hle : W ≤ ⊤),
        IsUnit (U.presheaf.map (homOfLE hle).op (h x)) := by
      rintro W rfl hle
      exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace (h x)
    exact key _ (Scheme.Opens.ι_image_top _) _
  exact hu.mul_right_eq_zero.1 (by rw [← map_mul, hh x, map_zero])

/- English proof (translation)
Introduce `q _ U X x ζ₀ ζ`. Rewrite using `[twGen_res]`. Conclude with `twGen_zero_indep _ _`.
-/
theorem TwRes0_of : TwRes0 := by
  intro q _ U X x ζ₀ ζ
  rw [twGen_res]
  exact twGen_zero_indep _ _

end LateralTheory.KummerTheory
