import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SInfIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.BW.BlockSaturationData

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)}

/- English proof (translation)
Take `⟨V, hV, hf⟩` from `b.summand`. Take `⟨π, hπ, -⟩` from `Dp.exCusp E r (mu1 E r) V hV`. Establish `hc : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ AutomorphicForm.centralCuspForms E r` using `fun s x => by`. Use `b.cen (Real.log s.1) x` as an intermediate fact. Unfold `zt at this`.

Simplify `this` using `only [Real.exp_log s.2]`. Establish `hm : b.f ∈ π.V`. Establish `: (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ Cm.carrier π`. Rewrite using `[hπ.carrier_eq]`. Conclude with `⟨hc, hf⟩`.

Conclude with `this`. Use `⟨V, hV, fun τ => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨m, h1, -⟩` from `Dp.sInfEx E r (mu1 E r) V hV τ`. Establish `h2 : GlobalTheory.UnitaryBC.HasInfCharGL π.V τ m` using `(Dp.sInfIff E r (mu1 E r) π V hπ τ m).1 h1`. Establish `hs : Submodule.span ℂ {b.f} ≠ ⊥` using `by simpa using b.ne`.

Establish `e : m = Finset.univ.val.map (b.Λ τ)`. Use `GlobalTheory.BcSpehProof.hasInfCharGL_unique hs (τ := τ) ⟨h2.1, fun u φ hφ => h2.2 u φ ?_⟩ ⟨by simp, fun u φ hφ => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.span_le.2 (Set.singleton_subset_iff.2 hm) hφ`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Rewrite using `[map_smul, b.inf, smul_comm, Multiset.map_map]`.

Both sides reduce to the same expression. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `h0` using `b.isSat w hw`. Establish `hx : (⟨b.f, hm⟩ : π.V) ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w r)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 h0.2.1 k hk)`.

Establish `hne : (⟨b.f, hm⟩ : π.V) ≠ 0` using `fun e => b.ne (congrArg Subtype.val e)`. Take `⟨B, hB⟩` from `GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨_, hx, hne⟩)`. Establish `h1 : GlobalTheory.LFun.IsSatVecGL w (rw r w) b.f B` using `(hB.2 _ hx hne).map π.V.subtype (fun _ _ => rfl) b.ne`. Establish `e` using `h1.unique h0`. Substitute `e` using the available equality.

Conclude with `(Dp.sSatIff E r (mu1 E r) π V hπ w _).2 ⟨_, rfl, hB⟩`.
-/
private theorem blo_at {r : ℕ} (b : Blo S r) : ∃ V, IsSummand (mu1 E r) V ∧
    At (mu1 E r) S V (fun τ => Finset.univ.val.map (b.Λ τ)) fun w => (b.sat w).map fun x : ℂˣ => (x : ℂ) := by
  obtain ⟨V, hV, hf⟩ := b.summand
  obtain ⟨π, hπ, -⟩ := Dp.exCusp E r (mu1 E r) V hV
  have hc : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ AutomorphicForm.centralCuspForms E r := fun s x => by
    have := b.cen (Real.log s.1) x
    unfold zt at this
    simpa only [Real.exp_log s.2] using this
  have hm : b.f ∈ π.V := by
    have : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ Cm.carrier π := by
      rw [hπ.carrier_eq]; exact ⟨hc, hf⟩
    exact this
  refine ⟨V, hV, fun τ => ?_, fun w hw => ?_⟩
  · obtain ⟨m, h1, -⟩ := Dp.sInfEx E r (mu1 E r) V hV τ
    have h2 : GlobalTheory.UnitaryBC.HasInfCharGL π.V τ m := (Dp.sInfIff E r (mu1 E r) π V hπ τ m).1 h1
    have hs : Submodule.span ℂ {b.f} ≠ ⊥ := by simpa using b.ne
    have e : m = Finset.univ.val.map (b.Λ τ) := by
      refine GlobalTheory.BcSpehProof.hasInfCharGL_unique hs (τ := τ) ⟨h2.1, fun u φ hφ => h2.2 u φ ?_⟩ ⟨by simp, fun u φ hφ => ?_⟩
      · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hm) hφ
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        rw [map_smul, b.inf, smul_comm, Multiset.map_map]
        rfl
    rw [e] at h1
    exact h1
  · have h0 := b.isSat w hw
    have hx : (⟨b.f, hm⟩ : π.V) ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w r) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 h0.2.1 k hk)
    have hne : (⟨b.f, hm⟩ : π.V) ≠ 0 := fun e => b.ne (congrArg Subtype.val e)
    obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨_, hx, hne⟩)
    have h1 : GlobalTheory.LFun.IsSatVecGL w (rw r w) b.f B := (hB.2 _ hx hne).map π.V.subtype (fun _ _ => rfl) b.ne
    have e := h1.unique h0
    subst e
    exact (Dp.sSatIff E r (mu1 E r) π V hπ w _).2 ⟨_, rfl, hB⟩

private def blk : {n : ℕ} → (d : Dat S n) → Fin d.len → Σ r, Blo S r
  | _, .nil => fun j => j.elim0
  | _, .cons b d => fun j => Fin.cases (motive := fun _ => Σ r, Blo S r) ⟨_, b⟩ (blk d) (j : Fin (d.len + 1))

/- English proof (translation)
The claim follows from `| _, .nil => rfl | _, .cons b d => by have := blk_sum d exact (Fin.sum_univ_succ (n := d.len) _).trans (congrArg (_ + ·) this)`.
-/
private theorem blk_sum : ∀ {n : ℕ} (d : Dat S n), ∑ j, (blk d j).1 = n
  | _, .nil => rfl
  | _, .cons b d => by
    have := blk_sum d
    exact (Fin.sum_univ_succ (n := d.len) _).trans (congrArg (_ + ·) this)

/- English proof (translation)
The claim follows from `| _, .nil, j => j.elim0 | _, .cons b d, j => by refine Fin.cases (motive := fun j : Fin (d.len + 1) => (Dat.cons b d).sat j = (blk (.cons b d) j).2.sat) rfl (fun i => blk_sat d i) j`.
-/
private theorem blk_sat : ∀ {n : ℕ} (d : Dat S n) (j : Fin d.len), d.sat j = (blk d j).2.sat
  | _, .nil, j => j.elim0
  | _, .cons b d, j => by
    refine Fin.cases (motive := fun j : Fin (d.len + 1) => (Dat.cons b d).sat j = (blk (.cons b d) j).2.sat) rfl
      (fun i => blk_sat d i) j

/- English proof (translation)
Simplify using `only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]`. Both sides reduce to the same expression.
-/
private theorem map_addCases {r s : ℕ} (f : Fin (r + s) → ℂ) :
    Finset.univ.val.map f = (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

/- English proof (translation)
The claim follows from `| _, .nil, _ => rfl | _, .cons b d, z => by have ih := blk_ms τ d fun j => z (j.succ : Fin (d.len + 1)) refine Eq.trans ?_ (Fin.sum_univ_succ (n := d.len) _).symm unfold msOf at ih ⊢ rw [map_addCases] congr 1 · rw [Multiset.map_map] refine Multiset.map_congr rfl fun i _ => ?_ hav …`.
-/
private theorem blk_ms (τ : E →+* ℂ) : ∀ {n : ℕ} (d : Dat S n) (z : Fin d.len → ℂ),
    msOf (d.ptL z) τ = ∑ j, (Finset.univ.val.map ((blk d j).2.Λ τ)).map (· + z j)
  | _, .nil, _ => rfl
  | _, .cons b d, z => by
    have ih := blk_ms τ d fun j => z (j.succ : Fin (d.len + 1))
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := d.len) _).symm
    unfold msOf at ih ⊢
    rw [map_addCases]
    congr 1
    · rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.castAdd _ i) = (0 : Fin (d.len + 1)) :=
        Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.castAdd _ i) = b.Λ τ i :=
        Fin.addCases_left (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)
    · refine Eq.trans ?_ ih
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.natAdd _ i) = ((d.idx i).succ : Fin (d.len + 1)) :=
        Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.natAdd _ i) = d.lam τ i :=
        Fin.addCases_right (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)

/- English proof (translation)
Use `choose V hV hA using fun j => blo_at (blk d j).2`. Use `⟨⟨d.len, h2, fun j => (blk d j).1, fun j => (blk d j).2.pos, blk_sum d, fun j => mu1 E _, V, hV⟩, fun z => ?_⟩` and prove the remaining obligations. Use `⟨z, _, _, hA, fun τ => blk_ms τ d z, fun w _ => ?_⟩` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[blk_sat, Multiset.map_map]`.

Both sides reduce to the same expression.
-/
theorem main (n : ℕ) (d : Dat S n) (h2 : 2 ≤ d.len) : ∃ b : Datum E n, ∀ z, b.Pt S (msOf (d.ptL z)) (d.ptS z) := by
  choose V hV hA using fun j => blo_at (blk d j).2
  refine ⟨⟨d.len, h2, fun j => (blk d j).1, fun j => (blk d j).2.pos, blk_sum d, fun j => mu1 E _, V, hV⟩, fun z => ?_⟩
  refine ⟨z, _, _, hA, fun τ => blk_ms τ d z, fun w _ => ?_⟩
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [blk_sat, Multiset.map_map]
  rfl

end UpperTheory.ConvolutionTheory.BW.BlockSaturationData

/- English proof (translation)
Introduce `E _ _ _ S n d h2`. Take `⟨b, hb⟩` from `UpperTheory.ConvolutionTheory.BW.BlockSaturationData.main n d h2`. Conclude with `⟨b, ⟨_, _, hb 0⟩, fun F _ hF z => hF _ _ (hb z)⟩`.
-/
theorem UpperTheory.ConvolutionTheory.BW.datDatum :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.DatDatum E := by
  intro E _ _ _ S n d h2
  obtain ⟨b, hb⟩ := UpperTheory.ConvolutionTheory.BW.BlockSaturationData.main n d h2
  exact ⟨b, ⟨_, _, hb 0⟩, fun F _ hF z => hF _ _ (hb z)⟩
