import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.HaarEqOneOfSq
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetOfInjectiveEndo

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨m, hm1, hlev⟩` from `exists_level (k := k) (n := n) g`. Use `set x := p.1 - c with hxdef`. Use `set v := p.2 with hvdef`. Use `set γ : ValueGroupWithZero k := valuation k (uniformizer k : k) ^ m with hγdef`. Establish `hγ0 : γ ≠ 0` using `pow_ne_zero _ (valuation_uniformizer_ne_zero k)`.

Use `set C := (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule with hCdef`. Use `set K : Subgroup (GL (Fin n) k) := congruenceSubgroup k n m ⊓ GzS Z with hKdef`. Use `set K' := K.map (MulAut.conj g).toMonoidHom with hK'def`. Use `set S := stab Z p with hSdef`. Use `set I := lat C γ with hIdef`.

Use `set I' := cj g I with hI'def`. Use `set Is := lat (cS Z x v) γ with hIsdef`. Use `set I's := cj g Is with hI'sdef`. Establish `hcZ : c ∈ Bz Z` using `fun a ha => hZ.1 a ha c hc`. Establish `hcu : ∀ u : GL (Fin n) k, u ∈ Gz Z → u.val * c = c * u.val` using `fun u hu => (hu c hc).symm`.

Establish `hginv : g⁻¹ ∈ Gz Z` using `Gz_inv Z hg`. Establish `hgx' : g⁻¹.val * x * g⁻¹⁻¹.val = t⁻¹ • x`. Rewrite using `[inv_inv]`. Establish `h1 : g⁻¹.val * (g.val * x * g⁻¹.val) * g.val = x` using `adL_inv_adL g x`. Rewrite `h1` using `[hgx, Matrix.mul_smul, Matrix.smul_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, inv_mul_cancel₀ ht, one_smul]`. Use `_ = t⁻¹ • x := by rw [h1]`. Establish `hgv' : g⁻¹.val *ᵥ v = v` using `by conv_lhs => rw [← hgv]`. Rewrite using `[mulVec_mulVec, Units.inv_mul, one_mulVec]`.

Establish `hSg : ∀ y, y ∈ cS Z x v ↔ g⁻¹.val * y * g.val ∈ cS Z x v`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `cS_inv Z x v g⁻¹ hginv t⁻¹ (inv_ne_zero ht) hgx' hgv' y hy` as an intermediate fact.

Rewrite `this` using `[adL_apply, inv_inv]`. Then use the resulting hypothesis. Introduce `hy`. Use `cS_inv Z x v g hg t ht hgx hgv _ hy` as an intermediate fact. Rewrite `this` using `[adL_apply, adL_adL_inv]`. Then use the resulting hypothesis. Establish `mK : ∀ u : GL (Fin n) k, u ∈ K ↔ u.val - 1 ∈ I` using `memK Z m hm1`.

Establish `mK' : ∀ u : GL (Fin n) k, u ∈ K' ↔ u.val - 1 ∈ I'`. Introduce `u`. Rewrite using `[memK', mK, mem_cj, conj_sub_one]`. Establish `mL : ∀ u : GL (Fin n) k, u ∈ K ⊓ K' ↔ u.val - 1 ∈ I ⊓ I'`. Introduce `u`.

Rewrite using `[Subgroup.mem_inf, AddSubgroup.mem_inf, mK, mK']`. Establish `mIs : ∀ y, y ∈ Is ↔ y ∈ I ∧ y ∈ cS Z x v`. Introduce `y`. Rewrite using `[mem_lat, mem_lat, mem_C_iff]`. Conclude with `⟨fun h => ⟨⟨h.1.1.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩`.

Establish `mI's : ∀ y, y ∈ I's ↔ y ∈ I' ∧ y ∈ cS Z x v`. Introduce `y`. Rewrite using `[mem_cj, mem_cj, mIs, ← hSg]`. Establish `hIB : ∀ y ∈ I, y ∈ Bz Z` using `fun y hy => (mem_C_iff Z y).1 (mem_lat.1 hy).1`. Establish `hI'B : ∀ y ∈ I', y ∈ Bz Z` using `fun y hy => by`.

Use `Bz_conj Z hg (hIB _ (mem_cj.1 hy))` as an intermediate fact. Rewrite `this` using `[adL_adL_inv]`. Then use the resulting hypothesis. Establish `mKS : ∀ u : GL (Fin n) k, u ∈ K ⊓ S ↔ u.val - 1 ∈ Is`. Introduce `u`. Rewrite using `[Subgroup.mem_inf, mIs, mK]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `hG : u ∈ Gz Z` using `(mem_Gz_iff Z u).2 (hIB _ h1)`. Conclude with `⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hIB _ h1)).1 h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Establish `hG : u ∈ Gz Z` using `(mem_Gz_iff Z u).2 (hIB _ h1)`. Conclude with `⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hIB _ h1)).2 h2⟩`. Establish `mK'S : ∀ u : GL (Fin n) k, u ∈ K' ⊓ S ↔ u.val - 1 ∈ I's`. Introduce `u`. Rewrite using `[Subgroup.mem_inf, mI's, mK']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `hG : u ∈ Gz Z` using `(mem_Gz_iff Z u).2 (hI'B _ h1)`. Conclude with `⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hI'B _ h1)).1 h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Establish `hG : u ∈ Gz Z` using `(mem_Gz_iff Z u).2 (hI'B _ h1)`. Conclude with `⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hI'B _ h1)).2 h2⟩`. Establish `mLS : ∀ u : GL (Fin n) k, u ∈ K ⊓ K' ⊓ S ↔ u.val - 1 ∈ Is ⊓ I's`. Introduce `u`. Rewrite using `[AddSubgroup.mem_inf, ← mKS, ← mK'S]`.

Simplify using `only [Subgroup.mem_inf]`. The claim follows by propositional logic. Establish `sI : ∀ y ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + y` using `fun y hy => by`. Take `⟨u, -, hu⟩` from `exists_unit (k := k) m hm1 y (mem_lat.1 hy).2`. Conclude with `⟨u, hu⟩`.

Establish `sI' : ∀ y ∈ I', ∃ u : GL (Fin n) k, u.val = 1 + y` using `fun y hy => by`. Take `⟨u, hu⟩` from `sI _ (mem_cj.1 hy)`. Use `⟨g * u * g⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, hu, mul_add, add_mul, mul_one, Units.mul_inv, adL_adL_inv]`. Establish `hmulJ : ∀ u : GL (Fin n) k, u ∈ Gz Z → u ∈ integralGL k n → g⁻¹ * u * g ∈ integralGL k n → ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I'`.

Introduce `u hG h1 h2 y hy`. Rewrite `hy`, the goal using `[AddSubgroup.mem_inf]`. Take `⟨hy1, hy2⟩` from `hy`. Use `⟨mem_lat.2 ⟨(mem_C_iff Z _).2 (Bz_mul Z hG (hIB _ hy1)), ent_mul (ent_integral h1) (mem_lat.1 hy1).2⟩, ?_⟩` and prove the remaining obligations. Rewrite `hy2`, the goal using `[mem_cj]`.

Establish `e : g⁻¹.val * (u.val * y) * g.val = (g⁻¹ * u * g).val * (g⁻¹.val * y * g.val)`. Simplify using `only [Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]`. Rewrite using `[e]`. Establish `hw : g⁻¹ * u * g ∈ GzS Z` using `(GzS Z).mul_mem ((GzS Z).mul_mem hginv hG) hg`. Conclude with `mem_lat.2 ⟨(mem_C_iff Z _).2 (Bz_mul Z hw (hIB _ hy2)), ent_mul (ent_integral h2) (mem_lat.1 hy2).2⟩`.

Establish `hmulJs : ∀ u : GL (Fin n) k, u ∈ Gz Z → u.val * x = x * u.val → u ∈ integralGL k n → g⁻¹ * u * g ∈ integralGL k n → ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's`. Introduce `u hG hux h1 h2 y hy`. Rewrite `hy`, the goal using `[AddSubgroup.mem_inf, mIs, mI's]`. Establish `hJ` using `hmulJ u hG h1 h2 y (AddSubgroup.mem_inf.2 ⟨hy.1.1, hy.2.1⟩)`. Rewrite `hJ` using `[AddSubgroup.mem_inf]`.

Establish `hS : u.val * y ∈ cS Z x v`. Take `⟨⟨hyB, hyx⟩, hyv⟩` from `hy.1.2`. Use `⟨⟨Bz_mul Z hG hyB, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, hyx, ← mul_assoc, hux, mul_assoc]`. Rewrite using `[← mulVec_mulVec, hyv, mulVec_zero]`.

Conclude with `⟨⟨hJ.1, hS⟩, ⟨hJ.2, hS⟩⟩`. Establish `hKint : ∀ u ∈ K, u ∈ Gz Z ∧ u ∈ integralGL k n ∧ g⁻¹ * u * g ∈ integralGL k n` using `fun u hu => ⟨hu.2, congruenceSubgroup_le k n m hu.1, (hlev u hu.1).1⟩`. Establish `hK'int : ∀ u ∈ K', u ∈ Gz Z ∧ u ∈ integralGL k n ∧ g⁻¹ * u * g ∈ integralGL k n`. Introduce `u hu`. Establish `hu' : g⁻¹ * u * g ∈ K` using `(memK' K g u).1 hu`.

Establish `e : g * (g⁻¹ * u * g) * g⁻¹ = u` using `by group`. Use `⟨?_, ?_, congruenceSubgroup_le k n m hu'.1⟩` and prove the remaining obligations. Rewrite using `[← e]`. Conclude with `(GzS Z).mul_mem ((GzS Z).mul_mem hg hu'.2) hginv`. Rewrite using `[← e]`.

Conclude with `(hlev _ hu'.1).2`. Establish `hmK : ∀ u ∈ K, ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I'` using `fun u hu => hmulJ u (hKint u hu).1 (hKint u hu).2.1 (hKint u hu).2.2`. Establish `hmK' : ∀ u ∈ K', ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I'` using `fun u hu => hmulJ u (hK'int u hu).1 (hK'int u hu).2.1 (hK'int u hu).2.2`. Establish `hmKS : ∀ u ∈ K ⊓ S, ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's` using `fun u hu => hmulJs u (hKint u hu.1).1 (comm_of_mem_cS Z x v u ((mIs _).1 ((mKS u).1 hu)).2) (hKint u hu.1).2.1 (hKint u hu.1).2.2`. Establish `hmK'S : ∀ u ∈ K' ⊓ S, ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's` using `fun u hu => hmulJs u (hK'int u hu.1).1 (comm_of_mem_cS Z x v u ((mI's _).1 ((mK'S u).1 hu)).2) (hK'int u hu.1).2.1 (hK'int u hu.1).2.2`.

Establish `e1 : (K ⊓ K').relIndex K = (I ⊓ I').relIndex I` using `relIndex_eq I (I ⊓ I') K (K ⊓ K') inf_le_left mK mL sI hmK`. Establish `e2 : (K ⊓ K').relIndex K' = (I ⊓ I').relIndex I'` using `relIndex_eq I' (I ⊓ I') K' (K ⊓ K') inf_le_right mK' mL sI' hmK'`. Establish `e3 : (K ⊓ K' ⊓ S).relIndex (K ⊓ S) = (Is ⊓ I's).relIndex Is` using `relIndex_eq Is (Is ⊓ I's) (K ⊓ S) (K ⊓ K' ⊓ S) inf_le_left mKS mLS (fun y hy => sI y ((mIs y).1 hy).1) hmKS`. Establish `e4 : (K ⊓ K' ⊓ S).relIndex (K' ⊓ S) = (Is ⊓ I's).relIndex I's` using `relIndex_eq I's (Is ⊓ I's) (K' ⊓ S) (K ⊓ K' ⊓ S) inf_le_right mK'S mLS (fun y hy => sI' y ((mI's y).1 hy).1) hmK'S`. Establish `hCinv` using `cC_inv Z g hg`.

Establish `hSinv` using `cS_inv Z x v g hg t ht hgx hgv`. Take `⟨nC1, -, rC⟩` from `hratio C γ hγ0 (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g C hCinv)) I I' (fun y => mem_lat) (mem_cj_iff_exists g C hCinv γ)`. Take `⟨nS1, nS2, rS⟩` from `hratio (cS Z x v) γ hγ0 (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv)) Is I's (fun y => mem_lat) (mem_cj_iff_exists g _ hSinv γ)`. Establish `dC : distribHaarChar k (LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g C hCinv))) = 1` using `haar_eq_one_of_sq _ (Units.ext (by rw [Units.val_pow_eq_pow_val, det_ofInjectiveEndo, Units.val_one]; exact det_C_sq Z τ hτ g hg))`. Rewrite `rC` using `[dC, NNReal.coe_one]`.

Use `⟨K, K ⊓ K', LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv)), det_ofInjectiveEndo g _ hSinv, inf_le_right, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k)) = ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k))`. Use extensionality with `h`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, hKdef, Subgroup.mem_inf]`. Conclude with `⟨fun hh => hh.1, fun hh => ⟨hh, h.2⟩⟩`.

Rewrite using `[this]`. Conclude with `(isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val`. Rewrite using `[hKdef, Subgroup.coe_inf]`. Conclude with `(isCompact_congruenceSubgroup k n m).inter_right (isClosed_Gz Z)`. Establish `: ((↑) : GzS Z → GL (Fin n) k) ⁻¹' ((K ⊓ K' : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k)) ∩ (fun h : GzS Z => g⁻¹ * (h : GL (Fin n) k) * g) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k))`.

Use extensionality with `h`. Establish `h2 : g⁻¹ * (h : GL (Fin n) k) * g ∈ GzS Z` using `(GzS Z).mul_mem ((GzS Z).mul_mem hginv h.2) hg`. Simplify using `only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_inf]`. Rewrite using `[memK', hKdef, Subgroup.mem_inf, Subgroup.mem_inf]`. Conclude with `⟨fun hh => ⟨hh.1.1, hh.2.1⟩, fun hh => ⟨⟨hh.1, h.2⟩, ⟨hh.2, h2⟩⟩⟩`.

Rewrite using `[this]`. Conclude with `((isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val).inter ((isOpen_congruenceSubgroup k n m).preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const))`. Introduce `a ha b hb`. Use `⟨K.mul_mem (K.mul_mem ha hb.1) (K.inv_mem ha), ?_⟩` and prove the remaining obligations. Establish `hb2 : g⁻¹ * b * g ∈ K` using `(memK' K g b).1 hb.2`.

Use `(memK' K g _).2 ?_` and prove the remaining obligations. Establish `e : g⁻¹ * (a * b * a⁻¹) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹` using `by group`. Rewrite using `[e]`. Take `⟨hG, -, hint⟩` from `hKint a ha`. Establish `hw : g⁻¹ * a * g ∈ GzS Z` using `(GzS Z).mul_mem ((GzS Z).mul_mem hginv hG) hg`.

Conclude with `⟨conj_mem_congruenceSubgroup k n hint hb2.1, (GzS Z).mul_mem ((GzS Z).mul_mem hw hb2.2) ((GzS Z).inv_mem hw)⟩`. Introduce `a ha b hb`. Use `⟨?_, K'.mul_mem (K'.mul_mem ha hb.2) (K'.inv_mem ha)⟩` and prove the remaining obligations. Take `⟨hG, hint, -⟩` from `hK'int a ha`. Conclude with `⟨conj_mem_congruenceSubgroup k n hint hb.1.1, (GzS Z).mul_mem ((GzS Z).mul_mem hG hb.1.2) ((GzS Z).inv_mem hG)⟩`.

Unfold `modul`. Rewrite using `[e1, e2, e3, e4]`. Use `set N : ℝ := (distribHaarChar k (LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv))) : ℝ) with hNdef`. Establish `hN : 0 < N` using `NNReal.coe_pos.2 distribHaarChar_pos`. Establish `ha : ((I ⊓ I').relIndex I : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 nC1`.

Establish `hb : ((Is ⊓ I's).relIndex Is : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 nS1`. Establish `hb' : ((Is ⊓ I's).relIndex I's : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 nS2`. Establish `ea : ((I ⊓ I').relIndex I' : ℝ) = (I ⊓ I').relIndex I` using `(div_eq_one_iff_eq ha).1 rC`. Establish `eb : ((Is ⊓ I's).relIndex I's : ℝ) = N * (Is ⊓ I's).relIndex Is` using `(div_eq_iff hb).1 rS`. Use `show _ = (N)⁻¹`.

Rewrite using `[ea, eb]`. Clear the denominators using the available nonvanishing facts.
-/
theorem modul_eqT (hratio : RatioP k n) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (hτ : IsTau Z τ)
    (c : Matrix (Fin n) (Fin n) k) (hc : c ∈ Z) (p : Sp k n) (hp : p.1 ∈ Bz Z)
    (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0)
    (hgx : g.val * (p.1 - c) * g⁻¹.val = t • (p.1 - c)) (hgv : g.val *ᵥ p.2 = p.2) :
    ∃ (K L : Subgroup (GL (Fin n) k)) (u : kˣ),
      (u : k) = LinearMap.det ((adL g).restrict (cS_inv Z (p.1 - c) p.2 g hg t ht hgx hgv)) ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧
      IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧
      L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      modul (stab Z p) K L g = (GlobalTheory.SplitWeil.nabs k u)⁻¹ := by
  classical
  obtain ⟨m, hm1, hlev⟩ := exists_level (k := k) (n := n) g
  set x := p.1 - c with hxdef
  set v := p.2 with hvdef
  set γ : ValueGroupWithZero k := valuation k (uniformizer k : k) ^ m with hγdef
  have hγ0 : γ ≠ 0 := pow_ne_zero _ (valuation_uniformizer_ne_zero k)
  set C := (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule with hCdef
  set K : Subgroup (GL (Fin n) k) := congruenceSubgroup k n m ⊓ GzS Z with hKdef
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'def
  set S := stab Z p with hSdef
  set I := lat C γ with hIdef
  set I' := cj g I with hI'def
  set Is := lat (cS Z x v) γ with hIsdef
  set I's := cj g Is with hI'sdef
  have hcZ : c ∈ Bz Z := fun a ha => hZ.1 a ha c hc
  have hcu : ∀ u : GL (Fin n) k, u ∈ Gz Z → u.val * c = c * u.val := fun u hu => (hu c hc).symm
  have hginv : g⁻¹ ∈ Gz Z := Gz_inv Z hg
  have hgx' : g⁻¹.val * x * g⁻¹⁻¹.val = t⁻¹ • x := by
    rw [inv_inv]
    have h1 : g⁻¹.val * (g.val * x * g⁻¹.val) * g.val = x := adL_inv_adL g x
    rw [hgx, Matrix.mul_smul, Matrix.smul_mul] at h1
    calc g⁻¹.val * x * g.val = t⁻¹ • (t • (g⁻¹.val * x * g.val)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • x := by rw [h1]
  have hgv' : g⁻¹.val *ᵥ v = v := by
    conv_lhs => rw [← hgv]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hSg : ∀ y, y ∈ cS Z x v ↔ g⁻¹.val * y * g.val ∈ cS Z x v := by
    intro y
    constructor
    · intro hy
      have := cS_inv Z x v g⁻¹ hginv t⁻¹ (inv_ne_zero ht) hgx' hgv' y hy
      rwa [adL_apply, inv_inv] at this
    · intro hy
      have := cS_inv Z x v g hg t ht hgx hgv _ hy
      rwa [adL_apply, adL_adL_inv] at this
  have mK : ∀ u : GL (Fin n) k, u ∈ K ↔ u.val - 1 ∈ I := memK Z m hm1
  have mK' : ∀ u : GL (Fin n) k, u ∈ K' ↔ u.val - 1 ∈ I' := by
    intro u
    rw [memK', mK, mem_cj, conj_sub_one]
  have mL : ∀ u : GL (Fin n) k, u ∈ K ⊓ K' ↔ u.val - 1 ∈ I ⊓ I' := by
    intro u
    rw [Subgroup.mem_inf, AddSubgroup.mem_inf, mK, mK']
  have mIs : ∀ y, y ∈ Is ↔ y ∈ I ∧ y ∈ cS Z x v := by
    intro y
    rw [mem_lat, mem_lat, mem_C_iff]
    exact ⟨fun h => ⟨⟨h.1.1.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  have mI's : ∀ y, y ∈ I's ↔ y ∈ I' ∧ y ∈ cS Z x v := by
    intro y
    rw [mem_cj, mem_cj, mIs, ← hSg]
  have hIB : ∀ y ∈ I, y ∈ Bz Z := fun y hy => (mem_C_iff Z y).1 (mem_lat.1 hy).1
  have hI'B : ∀ y ∈ I', y ∈ Bz Z := fun y hy => by
    have := Bz_conj Z hg (hIB _ (mem_cj.1 hy))
    rwa [adL_adL_inv] at this
  have mKS : ∀ u : GL (Fin n) k, u ∈ K ⊓ S ↔ u.val - 1 ∈ Is := by
    intro u
    rw [Subgroup.mem_inf, mIs, mK]
    constructor
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hIB _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hIB _ h1)).1 h2⟩
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hIB _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hIB _ h1)).2 h2⟩
  have mK'S : ∀ u : GL (Fin n) k, u ∈ K' ⊓ S ↔ u.val - 1 ∈ I's := by
    intro u
    rw [Subgroup.mem_inf, mI's, mK']
    constructor
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hI'B _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hI'B _ h1)).1 h2⟩
    · rintro ⟨h1, h2⟩
      have hG : u ∈ Gz Z := (mem_Gz_iff Z u).2 (hI'B _ h1)
      exact ⟨h1, (mem_stab_iff Z c p u (hcu u hG) (hI'B _ h1)).2 h2⟩
  have mLS : ∀ u : GL (Fin n) k, u ∈ K ⊓ K' ⊓ S ↔ u.val - 1 ∈ Is ⊓ I's := by
    intro u
    rw [AddSubgroup.mem_inf, ← mKS, ← mK'S]
    simp only [Subgroup.mem_inf]
    tauto
  have sI : ∀ y ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + y := fun y hy => by
    obtain ⟨u, -, hu⟩ := exists_unit (k := k) m hm1 y (mem_lat.1 hy).2
    exact ⟨u, hu⟩
  have sI' : ∀ y ∈ I', ∃ u : GL (Fin n) k, u.val = 1 + y := fun y hy => by
    obtain ⟨u, hu⟩ := sI _ (mem_cj.1 hy)
    refine ⟨g * u * g⁻¹, ?_⟩
    rw [Units.val_mul, Units.val_mul, hu, mul_add, add_mul, mul_one, Units.mul_inv, adL_adL_inv]
  have hmulJ : ∀ u : GL (Fin n) k, u ∈ Gz Z → u ∈ integralGL k n → g⁻¹ * u * g ∈ integralGL k n →
      ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I' := by
    intro u hG h1 h2 y hy
    rw [AddSubgroup.mem_inf] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨mem_lat.2 ⟨(mem_C_iff Z _).2 (Bz_mul Z hG (hIB _ hy1)), ent_mul (ent_integral h1) (mem_lat.1 hy1).2⟩, ?_⟩
    rw [mem_cj] at hy2 ⊢
    have e : g⁻¹.val * (u.val * y) * g.val = (g⁻¹ * u * g).val * (g⁻¹.val * y * g.val) := by
      simp only [Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
    rw [e]
    have hw : g⁻¹ * u * g ∈ GzS Z := (GzS Z).mul_mem ((GzS Z).mul_mem hginv hG) hg
    exact mem_lat.2 ⟨(mem_C_iff Z _).2 (Bz_mul Z hw (hIB _ hy2)), ent_mul (ent_integral h2) (mem_lat.1 hy2).2⟩
  have hmulJs : ∀ u : GL (Fin n) k, u ∈ Gz Z → u.val * x = x * u.val → u ∈ integralGL k n →
      g⁻¹ * u * g ∈ integralGL k n → ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's := by
    intro u hG hux h1 h2 y hy
    rw [AddSubgroup.mem_inf, mIs, mI's] at hy ⊢
    have hJ := hmulJ u hG h1 h2 y (AddSubgroup.mem_inf.2 ⟨hy.1.1, hy.2.1⟩)
    rw [AddSubgroup.mem_inf] at hJ
    have hS : u.val * y ∈ cS Z x v := by
      obtain ⟨⟨hyB, hyx⟩, hyv⟩ := hy.1.2
      refine ⟨⟨Bz_mul Z hG hyB, ?_⟩, ?_⟩
      · rw [mul_assoc, hyx, ← mul_assoc, hux, mul_assoc]
      · rw [← mulVec_mulVec, hyv, mulVec_zero]
    exact ⟨⟨hJ.1, hS⟩, ⟨hJ.2, hS⟩⟩
  have hKint : ∀ u ∈ K, u ∈ Gz Z ∧ u ∈ integralGL k n ∧ g⁻¹ * u * g ∈ integralGL k n := fun u hu =>
    ⟨hu.2, congruenceSubgroup_le k n m hu.1, (hlev u hu.1).1⟩
  have hK'int : ∀ u ∈ K', u ∈ Gz Z ∧ u ∈ integralGL k n ∧ g⁻¹ * u * g ∈ integralGL k n := by
    intro u hu
    have hu' : g⁻¹ * u * g ∈ K := (memK' K g u).1 hu
    have e : g * (g⁻¹ * u * g) * g⁻¹ = u := by group
    refine ⟨?_, ?_, congruenceSubgroup_le k n m hu'.1⟩
    · rw [← e]
      exact (GzS Z).mul_mem ((GzS Z).mul_mem hg hu'.2) hginv
    · rw [← e]
      exact (hlev _ hu'.1).2
  have hmK : ∀ u ∈ K, ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I' := fun u hu =>
    hmulJ u (hKint u hu).1 (hKint u hu).2.1 (hKint u hu).2.2
  have hmK' : ∀ u ∈ K', ∀ y ∈ I ⊓ I', u.val * y ∈ I ⊓ I' := fun u hu =>
    hmulJ u (hK'int u hu).1 (hK'int u hu).2.1 (hK'int u hu).2.2
  have hmKS : ∀ u ∈ K ⊓ S, ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's := fun u hu =>
    hmulJs u (hKint u hu.1).1 (comm_of_mem_cS Z x v u ((mIs _).1 ((mKS u).1 hu)).2)
      (hKint u hu.1).2.1 (hKint u hu.1).2.2
  have hmK'S : ∀ u ∈ K' ⊓ S, ∀ y ∈ Is ⊓ I's, u.val * y ∈ Is ⊓ I's := fun u hu =>
    hmulJs u (hK'int u hu.1).1 (comm_of_mem_cS Z x v u ((mI's _).1 ((mK'S u).1 hu)).2)
      (hK'int u hu.1).2.1 (hK'int u hu.1).2.2
  have e1 : (K ⊓ K').relIndex K = (I ⊓ I').relIndex I :=
    relIndex_eq I (I ⊓ I') K (K ⊓ K') inf_le_left mK mL sI hmK
  have e2 : (K ⊓ K').relIndex K' = (I ⊓ I').relIndex I' :=
    relIndex_eq I' (I ⊓ I') K' (K ⊓ K') inf_le_right mK' mL sI' hmK'
  have e3 : (K ⊓ K' ⊓ S).relIndex (K ⊓ S) = (Is ⊓ I's).relIndex Is :=
    relIndex_eq Is (Is ⊓ I's) (K ⊓ S) (K ⊓ K' ⊓ S) inf_le_left mKS mLS
      (fun y hy => sI y ((mIs y).1 hy).1) hmKS
  have e4 : (K ⊓ K' ⊓ S).relIndex (K' ⊓ S) = (Is ⊓ I's).relIndex I's :=
    relIndex_eq I's (Is ⊓ I's) (K' ⊓ S) (K ⊓ K' ⊓ S) inf_le_right mK'S mLS
      (fun y hy => sI' y ((mI's y).1 hy).1) hmK'S
  have hCinv := cC_inv Z g hg
  have hSinv := cS_inv Z x v g hg t ht hgx hgv
  obtain ⟨nC1, -, rC⟩ := hratio C γ hγ0 (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g C hCinv)) I I'
    (fun y => mem_lat) (mem_cj_iff_exists g C hCinv γ)
  obtain ⟨nS1, nS2, rS⟩ := hratio (cS Z x v) γ hγ0
    (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv)) Is I's
    (fun y => mem_lat) (mem_cj_iff_exists g _ hSinv γ)
  have dC : distribHaarChar k (LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g C hCinv))) = 1 :=
    haar_eq_one_of_sq _
      (Units.ext (by rw [Units.val_pow_eq_pow_val, det_ofInjectiveEndo, Units.val_one]; exact det_C_sq Z τ hτ g hg))
  rw [dC, NNReal.coe_one] at rC
  refine ⟨K, K ⊓ K', LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv)),
    det_ofInjectiveEndo g _ hSinv, inf_le_right, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_⟩
  · have : ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k)) =
        ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
      ext h
      simp only [Set.mem_preimage, SetLike.mem_coe, hKdef, Subgroup.mem_inf]
      exact ⟨fun hh => hh.1, fun hh => ⟨hh, h.2⟩⟩
    rw [this]
    exact (isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val
  · rw [hKdef, Subgroup.coe_inf]
    exact (isCompact_congruenceSubgroup k n m).inter_right (isClosed_Gz Z)
  · have : ((↑) : GzS Z → GL (Fin n) k) ⁻¹' ((K ⊓ K' : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) =
        ((↑) : GzS Z → GL (Fin n) k) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k)) ∩
          (fun h : GzS Z => g⁻¹ * (h : GL (Fin n) k) * g) ⁻¹' (congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
      ext h
      have h2 : g⁻¹ * (h : GL (Fin n) k) * g ∈ GzS Z := (GzS Z).mul_mem ((GzS Z).mul_mem hginv h.2) hg
      simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, Subgroup.mem_inf]
      rw [memK', hKdef, Subgroup.mem_inf, Subgroup.mem_inf]
      exact ⟨fun hh => ⟨hh.1.1, hh.2.1⟩, fun hh => ⟨⟨hh.1, h.2⟩, ⟨hh.2, h2⟩⟩⟩
    rw [this]
    exact ((isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val).inter
      ((isOpen_congruenceSubgroup k n m).preimage
        ((continuous_const.mul continuous_subtype_val).mul continuous_const))
  · intro a ha b hb
    refine ⟨K.mul_mem (K.mul_mem ha hb.1) (K.inv_mem ha), ?_⟩
    have hb2 : g⁻¹ * b * g ∈ K := (memK' K g b).1 hb.2
    refine (memK' K g _).2 ?_
    have e : g⁻¹ * (a * b * a⁻¹) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ := by group
    rw [e]
    obtain ⟨hG, -, hint⟩ := hKint a ha
    have hw : g⁻¹ * a * g ∈ GzS Z := (GzS Z).mul_mem ((GzS Z).mul_mem hginv hG) hg
    exact ⟨conj_mem_congruenceSubgroup k n hint hb2.1,
      (GzS Z).mul_mem ((GzS Z).mul_mem hw hb2.2) ((GzS Z).inv_mem hw)⟩
  · intro a ha b hb
    refine ⟨?_, K'.mul_mem (K'.mul_mem ha hb.2) (K'.inv_mem ha)⟩
    obtain ⟨hG, hint, -⟩ := hK'int a ha
    exact ⟨conj_mem_congruenceSubgroup k n hint hb.1.1,
      (GzS Z).mul_mem ((GzS Z).mul_mem hG hb.1.2) ((GzS Z).inv_mem hG)⟩
  · unfold modul
    rw [e1, e2, e3, e4]
    set N : ℝ := (distribHaarChar k (LinearEquiv.det (LinearEquiv.ofInjectiveEndo _ (adL_restrict_inj g _ hSinv))) : ℝ)
      with hNdef
    have hN : 0 < N := NNReal.coe_pos.2 distribHaarChar_pos
    have ha : ((I ⊓ I').relIndex I : ℝ) ≠ 0 := Nat.cast_ne_zero.2 nC1
    have hb : ((Is ⊓ I's).relIndex Is : ℝ) ≠ 0 := Nat.cast_ne_zero.2 nS1
    have hb' : ((Is ⊓ I's).relIndex I's : ℝ) ≠ 0 := Nat.cast_ne_zero.2 nS2
    have ea : ((I ⊓ I').relIndex I' : ℝ) = (I ⊓ I').relIndex I := (div_eq_one_iff_eq ha).1 rC
    have eb : ((Is ⊓ I's).relIndex I's : ℝ) = N * (Is ⊓ I's).relIndex Is := (div_eq_iff hb).1 rS
    show _ = (N)⁻¹
    rw [ea, eb]
    field_simp

end PositivityTheory.RgUd.TP.Nil.Orb.Mod
