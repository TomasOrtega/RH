import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticeRelativeLengthMapIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLenChainAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRelativeLengthSmulEqRankMulValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankAddValuationIntegerSubmoduleEqFinrankSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValIntStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbLen

/- English proof (translation)
Take `⟨n, b, b', A, -, hr⟩` from `h`. Establish `h0 : (0 : WithTop ℝ) ≤ v (A.det : C)` using `(mem_addValuationIntegerRing_iff v _).1 A.det.2`. Rewrite `h0` using `[hr]`. Conclude with `h0` after adjusting the coercions.
-/
theorem relLen_nonneg {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : Type}
    [AddCommGroup M] [Module (Int0 v) M] {X' X : Submodule (Int0 v) M} {r : ℝ}
    (h : RelLen v X' X r) : 0 ≤ r := by
  obtain ⟨n, b, b', A, -, hr⟩ := h
  have h0 : (0 : WithTop ℝ) ≤ v (A.det : C) := (mem_addValuationIntegerRing_iff v _).1 A.det.2
  rw [hr] at h0
  exact_mod_cast h0

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih]`.
-/
theorem addVal_prod {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (s : Finset ι) (f : ι → C) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Unfold `LengthIdentities`. Take `⟨hd0, hker, hkerrange, hXker, hAX, -, -, hprojX, hHX, hFX, htf, g, helem⟩` from `GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hsat τ`. Take `⟨fF, fX, fK, fH, -, fFt, fKP⟩` from `GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hsat τ`. Take `⟨-, -, hlc, hevc, -, -, -⟩` from `GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ`. Establish `m1 : ∀ x : Fin N → RS a, x ∈ eigSub a τ (Fin N → RS a) ↔ lin a τ • x = 0`.

Introduce `x`. Simplify using `[eigSub, kerMul]`. Establish `m2 : ∀ x : Fin N → RS a, x ∈ preEig a Fil τ ↔ lin a τ • x ∈ Fil`. Introduce `x`. Simplify using `[preEig, mulR]`.

Establish `m3 : ∀ x : Fin N → RS a, x ∈ filKer a Fil τ ↔ x ∈ Fil ∧ cofac a τ • x = 0`. Introduce `x`. Simplify using `[filKer, mulR]`. Establish `m4 : ∀ x : Fil, x ∈ eigSub a τ Fil ↔ lin a τ • (x : Fin N → RS a) = 0`. Introduce `x`.

Simplify using `[eigSub, kerMul, Subtype.ext_iff]`. Generalize the expression as in `hd : ev a τ (cofac a τ) = d at hd0 helem hevc`. Establish `hlinP : ∀ x : Fin N → RS a, lin a τ • (cofac a τ • x) = 0`. Introduce `x`. Rewrite using `[smul_smul, hlc, zero_smul]`.

Establish `hPh : ∀ x : Fin N → RS a, lin a τ • x = 0 → d • x = cofac a τ • x`. Introduce `x h`. Rewrite using `[helem, h, smul_zero, sub_zero]`. Establish `hcA : ∀ x, comp a N τ (lin a τ • x) = 0`. Introduce `x`.

Establish `: lin a τ • x ∈ LinearMap.ker (comp a N τ)` using `by rw [hkerrange]; exact ⟨x, rfl⟩`. Conclude with `this`. Establish `hcP : ∀ x, comp a N τ (cofac a τ • x) = d • comp a N τ x`. Introduce `x`. Rewrite using `[show d • comp a N τ x = comp a N τ (d • x) from (map_smul (comp a N τ) d x).symm, helem, map_sub, smul_comm g (lin a τ) x, hcA, sub_zero]`.

Establish `hker' : ∀ x, comp a N τ x = 0 ↔ cofac a τ • x = 0` using `hker`. Establish `hkerA : ∀ x, mulR a N (lin a τ) x = 0 → x ∈ eigSub a τ (Fin N → RS a)` using `fun x h => (m1 x).2 h`. Establish `hIinj : Function.Injective (incl a Fil)` using `fun x y h => Subtype.ext h`. Establish `htfQ : ∀ (c : Int0 v) (y : (Fin N → RS a) ⧸ Fil), c ≠ 0 → c • y = 0 → y = 0`. Introduce `c y hc h`.

Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H x`. Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (hsat c x hc h)`. Establish `htfF : ∀ (c : Int0 v) (y : Fil), c ≠ 0 → c • y = 0 → y = 0`.

Introduce `c y hc h`. Conclude with `Subtype.ext (htf c y hc (congrArg Subtype.val h))`. Establish `htfO : ∀ (c : Int0 v) (y : Fin N → Int0 v), c ≠ 0 → c • y = 0 → y = 0`. Introduce `c y hc h`. Conclude with `(smul_eq_zero.mp h).resolve_left hc`.

Establish `fgF : (Fil.restrictScalars (Int0 v)).FG` using `Module.Finite.iff_fg.mp fF`. Establish `fgH : (eigSub a τ (Fin N → RS a)).FG` using `Module.Finite.iff_fg.mp fH`. Establish `fgK : (filKer a Fil τ).FG` using `Module.Finite.iff_fg.mp fK`. Establish `fB : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v))` using `Module.Finite.iff_fg.mpr (fgH.sup fgF)`. Establish `hBX : eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ` using `sup_le hHX hFX`.

Establish `hdB : ∀ x ∈ preEig a Fil τ, d • x ∈ eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)`. Introduce `x hx`. Rewrite using `[helem]`. Use `Submodule.sub_mem_sup ?_ ?_` and prove the remaining obligations. Conclude with `(m1 _).2 (hlinP x)`.

Conclude with `Fil.smul_mem g ((m2 x).1 hx)`. Take `⟨δ, hδ⟩` from `GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htf _ _ hBX fX fB d hd0 hdB`. Establish `hmapB_proj : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (proj a Fil) = (eigSub a τ (Fin N → RS a)).map (proj a Fil)`. Rewrite using `[Submodule.map_sup]`. Establish `: (Fil.restrictScalars (Int0 v)).map (proj a Fil) = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(Submodule.mem_bot _).2 ((Submodule.Quotient.mk_eq_zero _).2 hx)`. Rewrite using `[this, sup_bot_eq]`. Establish `ha1 : RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil)) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ`.

Use `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfQ (proj a Fil) _ _ hBX ?_ fX fB δ).1 hδ` as an intermediate fact. Rewrite `this` using `[hmapB_proj, hprojX]`. Then use the resulting hypothesis. Introduce and unpack `x ⟨-, hx⟩`. Conclude with `Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).1 hx)`. Establish `hHA : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(Submodule.mem_bot _).2 ((m1 x).1 hx)`. Establish `hmapB_A : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) = (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ))`. Rewrite using `[Submodule.map_sup, hHA, bot_sup_eq]`.

Establish `hb0 : RelLen v ((Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ))) (filKer a Fil τ) δ`. Use `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hBX ?_ fX fB δ).1 hδ` as an intermediate fact. Rewrite `this` using `[hmapB_A, hAX]`. Then use the resulting hypothesis. Introduce and unpack `x ⟨-, hx⟩`. Conclude with `Submodule.mem_sup_left (hkerA x hx)`.

Establish `hIm1 : (imMul a (lin a τ) Fil).map (incl a Fil) = (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨w, rfl⟩, rfl⟩`. Conclude with `⟨w, w.2, rfl⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨lin a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩`. Establish `hIm2 : (kerMul a (cofac a τ) Fil).map (incl a Fil) = filKer a Fil τ`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(m3 _).2 ⟨y.2, by simpa [kerMul, Subtype.ext_iff, incl] using hy⟩`. Introduce `hz`. Take `⟨hz1, hz2⟩` from `(m3 z).1 hz`. Conclude with `⟨⟨z, hz1⟩, by simpa [kerMul, Subtype.ext_iff] using hz2, rfl⟩`.

Establish `hfgImLin : (imMul a (lin a τ) Fil).FG` using `Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm1]; exact fgF.map _)`. Establish `hle2 : imMul a (lin a τ) Fil ≤ kerMul a (cofac a τ) Fil`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `show cofac a τ • lin a τ • y = 0`. Rewrite using `[smul_smul, mul_comm, hlc, zero_smul]`.

Establish `hb : RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ`. Use `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htf (incl a Fil) _ _ hle2 ?_ fKP (Module.Finite.iff_fg.mpr hfgImLin) δ).2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨-, hx⟩`. Establish `: x = 0` using `hIinj (by rw [map_zero]; exact hx)`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Rewrite using `[hIm1, hIm2]` and apply the resulting hypothesis. Establish `hIm3 : (imMul a (cofac a τ) Fil).map (incl a Fil) = (Fil.restrictScalars (Int0 v)).map (mulR a N (cofac a τ))`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, ⟨w, rfl⟩, rfl⟩`. Conclude with `⟨w, w.2, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩`. Establish `hfgImP : (imMul a (cofac a τ) Fil).FG` using `Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm3]; exact fgF.map _)`.

Establish `hle3 : imMul a (cofac a τ) Fil ≤ eigSub a τ Fil`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `(m4 _).2 (hlinP y)`. Establish `hd3 : ∀ y ∈ eigSub a τ Fil, d • y ∈ imMul a (cofac a τ) Fil`. Introduce `y hy`.

Use `⟨y, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show cofac a τ • (y : Fin N → RS a) = d • (y : Fin N → RS a)`. Rewrite using `[hPh _ ((m4 y).1 hy)]`. Take `⟨e₂, he₂⟩` from `GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfF _ _ hle3 fFt (Module.Finite.iff_fg.mpr hfgImP) d hd0 hd3`. Establish `fgE : (eigQuot a Fil τ).FG` using `fgF.map _`.

Establish `fE : Module.Finite (Int0 v) (eigQuot a Fil τ)` using `Module.Finite.iff_fg.mpr fgE`. Establish `hfgFt : (eigSub a τ Fil).FG` using `Module.Finite.iff_fg.mp fFt`. Establish `fCt : Module.Finite (Int0 v) ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)))` using `Module.Finite.iff_fg.mpr (hfgFt.map _)`. Establish `hle4 : (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) ≤ eigQuot a Fil τ`. Introduce and unpack `_ ⟨y, -, rfl⟩`.

Conclude with `⟨y, y.2, rfl⟩`. Establish `hd4 : ∀ z ∈ eigQuot a Fil τ, d • z ∈ (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, (m4 _).2 (hlinP x), hcP x⟩`. Take `⟨m, hm⟩` from `GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfO _ _ hle4 fE fCt d hd0 hd4`.

Establish `hIm5 : (imMul a (cofac a τ) Fil).map ((comp a N τ).comp (incl a Fil)) = (eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, rfl⟩, rfl⟩`. Conclude with `⟨comp a N τ y, ⟨y, y.2, rfl⟩, (hcP y).symm⟩`.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, hcP x⟩`. Establish `he5 : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d)) ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) e₂`. Use `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htfO ((comp a N τ).comp (incl a Fil)) _ _ hle3 ?_ fFt (Module.Finite.iff_fg.mpr hfgImP) e₂).1 he₂` as an intermediate fact. Rewrite `this` using `[hIm5]`. Then use the resulting hypothesis.

Introduce and unpack `y ⟨hy, hy0⟩`. Establish `h1 : cofac a τ • (y : Fin N → RS a) = 0` using `(hker' _).1 hy0`. Establish `h2 : d • (y : Fin N → RS a) = 0` using `by rw [hPh _ ((m4 y).1 hy), h1]`. Establish `: y = 0` using `Subtype.ext (htf d _ hd0 h2)`. Rewrite using `[this]`.

Conclude with `Submodule.zero_mem _`. Establish `hme : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d)) (eigQuot a Fil τ) (m + e₂)` using `GlobalTheory.T.relLen_trans_add C v _ _ _ _ m e₂ he5 hm`. Establish `hdC0 : (d : C) ≠ 0` using `fun h => hd0 (Subtype.ext h)`. Establish `hvd : v (d : C) ≠ ⊤` using `fun h => hdC0 ((AddValuation.top_iff v).1 h)`. Take `⟨rd, hrd⟩` from `WithTop.ne_top_iff_exists.1 hvd`.

Establish `hsc` using `GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation C v _ htfO (eigQuot a Fil τ) fE d rd hrd.symm`. Establish `hsum : m + e₂ = (finrank (Int0 v) (eigQuot a Fil τ) : ℝ) * rd` using `RelLen.unique v hme hsc`. Establish `hfr : finrank (Int0 v) (eigQuot a Fil τ) = eigRank v a Fil τ` using `GlobalTheory.T.finrank_int0_submodule_eq_finrank_span C v N _ fE`. Establish `hdC : ((d : Int0 v) : C) = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C))`. Rewrite using `[hevc]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hvdeq : vd v a τ = (rd : WithTop ℝ)`. Unfold `vd`. Rewrite using `[← hdC, hrd]`.

Establish `hjr : eigRank v a Fil τ • vd v a τ = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ)`. Rewrite using `[hvdeq, ← WithTop.coe_nsmul, nsmul_eq_mul]`. Establish `hKc : (filKer a Fil τ).map (comp a N τ) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `(Submodule.mem_bot _).2 ((hker' x).2 ((m3 x).1 hx).2)`. Establish `hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v)` using `fun x hx => ((m3 x).1 hx).1`. Establish `hD'F : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ ≤ Fil.restrictScalars (Int0 v)` using `sup_le inf_le_left hKF`. Establish `hDB : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤ eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)` using `sup_le_sup_left hKF _`. Establish `hFHt : Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a) = (eigSub a τ Fil).map (incl a Fil)`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz1, hz2⟩`. Conclude with `⟨⟨z, hz1⟩, (m4 _).2 ((m1 z).1 hz2), rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨y.2, (m1 _).2 ((m4 y).1 hy)⟩`. Establish `fD' : Module.Finite (Int0 v) ↥((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ)` using `Module.Finite.iff_fg.mpr (by rw [hFHt]; exact (hfgFt.map _).sup fgK)`. Establish `fD : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ)` using `Module.Finite.iff_fg.mpr (fgH.sup fgK)`. Establish `hmapcD' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map (comp a N τ) = (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))`. Rewrite using `[Submodule.map_sup, hKc, sup_bot_eq, hFHt, Submodule.map_comp]`.

Establish `s1 : RelLen v ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ) (Fil.restrictScalars (Int0 v)) m`. Use `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hD'F ?_ fF fD' m).2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hxF, hx0⟩`. Conclude with `Submodule.mem_sup_right ((m3 x).2 ⟨hxF, (hker' x).1 hx0⟩)`. Rewrite using `[hmapcD']`.

Conclude with `hm`. Establish `s2` using `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hD'F (by`. Introduce and unpack `x ⟨hxF, hx0⟩`. Conclude with `Submodule.mem_sup_left ⟨hxF, hkerA x hx0⟩) fF fD' m).1 s1`. Establish `hDA' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) = (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ))`.

Establish `h0 : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥` using `le_bot_iff.1 (hHA ▸ Submodule.map_mono inf_le_right)`. Rewrite using `[Submodule.map_sup, Submodule.map_sup, h0, hHA]`. Establish `s3 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)) m`. Use `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hDB ?_ fB fD m).2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨-, hx0⟩`.

Conclude with `Submodule.mem_sup_left (hkerA x hx0)`. Rewrite using `[← hDA', hmapB_A]`. Conclude with `s2`. Establish `s4` using `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hDB (by`. Introduce and unpack `x ⟨hxB, hx0⟩`.

Take `⟨h, hh, f', hf', rfl⟩` from `Submodule.mem_sup.1 hxB`. Establish `hP0 : cofac a τ • (h + f') = 0` using `(hker' _).1 hx0`. Establish `hdh : d • h ∈ Fil`. Rewrite using `[hPh h ((m1 h).1 hh)]`. Establish `e1 : cofac a τ • h = -(cofac a τ • f')` using `eq_neg_of_add_eq_zero_left (by rw [← smul_add]; exact hP0)`.

Rewrite using `[e1]`. Conclude with `Fil.neg_mem (Fil.smul_mem _ hf')`. Establish `hhF` using `hsat d h hd0 hdh`. Conclude with `Submodule.mem_sup_right ((m3 _).2 ⟨Fil.add_mem hhF hf', hP0⟩)) fB fD m).1 s3`. Establish `hDc : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) = (eigSub a τ (Fin N → RS a)).map (comp a N τ)`.

Rewrite using `[Submodule.map_sup, hKc, sup_bot_eq]`. Rewrite `s4` using `[hDc]`. Establish `s5` using `(GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hBX (by`. Introduce and unpack `x ⟨hxX, hx0⟩`. Conclude with `Submodule.mem_sup_right (hXker ⟨hxX, hx0⟩)) fX fB δ).1 hδ`.

Establish `s6` using `GlobalTheory.T.relLen_trans_add C v _ _ _ _ δ m s4 s5`. Establish `hrδ : r = δ + m` using `RelLen.unique v hlen s6`. Use `⟨δ, e₂, m, ha1, hb, he₂, hm, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum, hfr, hjr]`. Introduce `hall`.

Establish `hy : yExp v a Fil τ = eigRank v a Fil τ • vd v a τ`. Unfold `yExp vd`. Rewrite using `[Finset.sum_congr rfl (fun s _ => by rw [hall s]), ← Finset.smul_sum, addVal_prod v]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun s _ => v.map_sub_swap _ _)`.

Establish `hrj : r = (eigRank v a Fil τ : ℝ) * rd`. Establish `: (r : WithTop ℝ) = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ)`. Rewrite using `[hr, hy, hjr]`. Conclude with `this` after adjusting the coercions. Establish `hδ0` using `relLen_nonneg hδ`.

Establish `hm0` using `relLen_nonneg hm`. Establish `he0` using `relLen_nonneg he₂`. Rewrite `hsum` using `[hfr]`. Rewrite using `[hjr]`. Use `⟨hδ0, ?_, hm0, ?_⟩` and prove the remaining obligations.

Conclude with `WithTop.coe_le_coe.2 (by linarith)`. Conclude with `WithTop.coe_le_coe.2 (by linarith)`.
-/
theorem herbrand_lengthIdentities_auxiliary_bound (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type)
    [Fintype S] [DecidableEq S] (a : S → Int0 v) (ha : Function.Injective a) (N : ℕ)
    (Fil : Submodule (RS a) (Fin N → RS a))
    (hsat : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) (τ : S) (r : ℝ)
    (hr : (r : WithTop ℝ) = yExp v a Fil τ)
    (hlen : RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ))
      ((preEig a Fil τ).map (comp a N τ)) r) :
    LengthIdentities v a Fil τ := by
  unfold LengthIdentities
  obtain ⟨hd0, hker, hkerrange, hXker, hAX, -, -, hprojX, hHX, hFX, htf, g, helem⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hsat τ
  obtain ⟨fF, fX, fK, fH, -, fFt, fKP⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hsat τ
  obtain ⟨-, -, hlc, hevc, -, -, -⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have m1 : ∀ x : Fin N → RS a, x ∈ eigSub a τ (Fin N → RS a) ↔ lin a τ • x = 0 := by
    intro x; simp [eigSub, kerMul]
  have m2 : ∀ x : Fin N → RS a, x ∈ preEig a Fil τ ↔ lin a τ • x ∈ Fil := by
    intro x; simp [preEig, mulR]
  have m3 : ∀ x : Fin N → RS a, x ∈ filKer a Fil τ ↔ x ∈ Fil ∧ cofac a τ • x = 0 := by
    intro x; simp [filKer, mulR]
  have m4 : ∀ x : Fil, x ∈ eigSub a τ Fil ↔ lin a τ • (x : Fin N → RS a) = 0 := by
    intro x; simp [eigSub, kerMul, Subtype.ext_iff]
  generalize hd : ev a τ (cofac a τ) = d at hd0 helem hevc
  have hlinP : ∀ x : Fin N → RS a, lin a τ • (cofac a τ • x) = 0 := by
    intro x; rw [smul_smul, hlc, zero_smul]
  have hPh : ∀ x : Fin N → RS a, lin a τ • x = 0 → d • x = cofac a τ • x := by
    intro x h; rw [helem, h, smul_zero, sub_zero]
  have hcA : ∀ x, comp a N τ (lin a τ • x) = 0 := by
    intro x
    have : lin a τ • x ∈ LinearMap.ker (comp a N τ) := by rw [hkerrange]; exact ⟨x, rfl⟩
    exact this
  have hcP : ∀ x, comp a N τ (cofac a τ • x) = d • comp a N τ x := by
    intro x
    rw [show d • comp a N τ x = comp a N τ (d • x) from (map_smul (comp a N τ) d x).symm, helem,
      map_sub, smul_comm g (lin a τ) x, hcA, sub_zero]
  have hker' : ∀ x, comp a N τ x = 0 ↔ cofac a τ • x = 0 := hker
  have hkerA : ∀ x, mulR a N (lin a τ) x = 0 → x ∈ eigSub a τ (Fin N → RS a) := fun x h => (m1 x).2 h
  have hIinj : Function.Injective (incl a Fil) := fun x y h => Subtype.ext h
  have htfQ : ∀ (c : Int0 v) (y : (Fin N → RS a) ⧸ Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero _).2 (hsat c x hc h)
  have htfF : ∀ (c : Int0 v) (y : Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    exact Subtype.ext (htf c y hc (congrArg Subtype.val h))
  have htfO : ∀ (c : Int0 v) (y : Fin N → Int0 v), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h; exact (smul_eq_zero.mp h).resolve_left hc
  have fgF : (Fil.restrictScalars (Int0 v)).FG := Module.Finite.iff_fg.mp fF
  have fgH : (eigSub a τ (Fin N → RS a)).FG := Module.Finite.iff_fg.mp fH
  have fgK : (filKer a Fil τ).FG := Module.Finite.iff_fg.mp fK
  have fB : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)) :=
    Module.Finite.iff_fg.mpr (fgH.sup fgF)

  have hBX : eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ :=
    sup_le hHX hFX
  have hdB : ∀ x ∈ preEig a Fil τ,
      d • x ∈ eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) := by
    intro x hx
    rw [helem]
    refine Submodule.sub_mem_sup ?_ ?_
    · exact (m1 _).2 (hlinP x)
    · exact Fil.smul_mem g ((m2 x).1 hx)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htf _ _ hBX fX fB d hd0 hdB

  have hmapB_proj : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (proj a Fil) =
      (eigSub a τ (Fin N → RS a)).map (proj a Fil) := by
    rw [Submodule.map_sup]
    have : (Fil.restrictScalars (Int0 v)).map (proj a Fil) = ⊥ := by
      rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).2 ((Submodule.Quotient.mk_eq_zero _).2 hx)
    rw [this, sup_bot_eq]
  have ha1 : RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil))
      (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfQ (proj a Fil) _ _ hBX ?_ fX fB δ).1 hδ
    · rwa [hmapB_proj, hprojX] at this
    · rintro x ⟨-, hx⟩
      exact Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).1 hx)

  have hHA : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ := by
    rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot _).2 ((m1 x).1 hx)
  have hmapB_A : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) := by
    rw [Submodule.map_sup, hHA, bot_sup_eq]
  have hb0 : RelLen v ((Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ))) (filKer a Fil τ) δ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hBX ?_ fX fB δ).1 hδ
    · rwa [hmapB_A, hAX] at this
    · rintro x ⟨-, hx⟩; exact Submodule.mem_sup_left (hkerA x hx)
  have hIm1 : (imMul a (lin a τ) Fil).map (incl a Fil) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) := by
    ext z; constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨lin a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hIm2 : (kerMul a (cofac a τ) Fil).map (incl a Fil) = filKer a Fil τ := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩
      exact (m3 _).2 ⟨y.2, by simpa [kerMul, Subtype.ext_iff, incl] using hy⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := (m3 z).1 hz
      exact ⟨⟨z, hz1⟩, by simpa [kerMul, Subtype.ext_iff] using hz2, rfl⟩
  have hfgImLin : (imMul a (lin a τ) Fil).FG :=
    Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm1]; exact fgF.map _)
  have hle2 : imMul a (lin a τ) Fil ≤ kerMul a (cofac a τ) Fil := by
    rintro _ ⟨y, rfl⟩
    show cofac a τ • lin a τ • y = 0
    rw [smul_smul, mul_comm, hlc, zero_smul]
  have hb : RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htf (incl a Fil) _ _ hle2 ?_ fKP
      (Module.Finite.iff_fg.mpr hfgImLin) δ).2 ?_
    · rintro x ⟨-, hx⟩
      have : x = 0 := hIinj (by rw [map_zero]; exact hx)
      rw [this]; exact Submodule.zero_mem _
    · rwa [hIm1, hIm2]

  have hIm3 : (imMul a (cofac a τ) Fil).map (incl a Fil) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (cofac a τ)) := by
    ext z; constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hfgImP : (imMul a (cofac a τ) Fil).FG :=
    Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm3]; exact fgF.map _)
  have hle3 : imMul a (cofac a τ) Fil ≤ eigSub a τ Fil := by
    rintro _ ⟨y, rfl⟩
    exact (m4 _).2 (hlinP y)
  have hd3 : ∀ y ∈ eigSub a τ Fil, d • y ∈ imMul a (cofac a τ) Fil := by
    intro y hy
    refine ⟨y, Subtype.ext ?_⟩
    show cofac a τ • (y : Fin N → RS a) = d • (y : Fin N → RS a)
    rw [hPh _ ((m4 y).1 hy)]
  obtain ⟨e₂, he₂⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfF _ _ hle3 fFt (Module.Finite.iff_fg.mpr hfgImP) d hd0 hd3

  have fgE : (eigQuot a Fil τ).FG := fgF.map _
  have fE : Module.Finite (Int0 v) (eigQuot a Fil τ) := Module.Finite.iff_fg.mpr fgE
  have hfgFt : (eigSub a τ Fil).FG := Module.Finite.iff_fg.mp fFt
  have fCt : Module.Finite (Int0 v) ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) :=
    Module.Finite.iff_fg.mpr (hfgFt.map _)
  have hle4 : (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) ≤ eigQuot a Fil τ := by
    rintro _ ⟨y, -, rfl⟩; exact ⟨y, y.2, rfl⟩
  have hd4 : ∀ z ∈ eigQuot a Fil τ, d • z ∈ (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, (m4 _).2 (hlinP x), hcP x⟩
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfO _ _ hle4 fE fCt d hd0 hd4

  have hIm5 : (imMul a (cofac a τ) Fil).map ((comp a N τ).comp (incl a Fil)) =
      (eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d) := by
    ext z; constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨comp a N τ y, ⟨y, y.2, rfl⟩, (hcP y).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, hcP x⟩
  have he5 : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d))
      ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) e₂ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htfO ((comp a N τ).comp (incl a Fil)) _ _ hle3 ?_ fFt
      (Module.Finite.iff_fg.mpr hfgImP) e₂).1 he₂
    · rwa [hIm5] at this
    · rintro y ⟨hy, hy0⟩
      have h1 : cofac a τ • (y : Fin N → RS a) = 0 := (hker' _).1 hy0
      have h2 : d • (y : Fin N → RS a) = 0 := by rw [hPh _ ((m4 y).1 hy), h1]
      have : y = 0 := Subtype.ext (htf d _ hd0 h2)
      rw [this]; exact Submodule.zero_mem _
  have hme : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d))
      (eigQuot a Fil τ) (m + e₂) :=
    GlobalTheory.T.relLen_trans_add C v _ _ _ _ m e₂ he5 hm
  have hdC0 : (d : C) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hvd : v (d : C) ≠ ⊤ := fun h => hdC0 ((AddValuation.top_iff v).1 h)
  obtain ⟨rd, hrd⟩ := WithTop.ne_top_iff_exists.1 hvd
  have hsc := GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation C v _ htfO (eigQuot a Fil τ) fE d rd hrd.symm
  have hsum : m + e₂ = (finrank (Int0 v) (eigQuot a Fil τ) : ℝ) * rd := RelLen.unique v hme hsc
  have hfr : finrank (Int0 v) (eigQuot a Fil τ) = eigRank v a Fil τ := GlobalTheory.T.finrank_int0_submodule_eq_finrank_span C v N _ fE
  have hdC : ((d : Int0 v) : C) = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
    rw [hevc]; push_cast; rfl
  have hvdeq : vd v a τ = (rd : WithTop ℝ) := by
    unfold vd; rw [← hdC, hrd]
  have hjr : eigRank v a Fil τ • vd v a τ = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ) := by
    rw [hvdeq, ← WithTop.coe_nsmul, nsmul_eq_mul]

  have hKc : (filKer a Fil τ).map (comp a N τ) = ⊥ := by
    rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot _).2 ((hker' x).2 ((m3 x).1 hx).2)
  have hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v) := fun x hx => ((m3 x).1 hx).1
  have hD'F : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ ≤
      Fil.restrictScalars (Int0 v) := sup_le inf_le_left hKF
  have hDB : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤
      eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) := sup_le_sup_left hKF _
  have hFHt : Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a) =
      (eigSub a τ Fil).map (incl a Fil) := by
    ext z; constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, hz1⟩, (m4 _).2 ((m1 z).1 hz2), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (m1 _).2 ((m4 y).1 hy)⟩
  have fD' : Module.Finite (Int0 v)
      ↥((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ) :=
    Module.Finite.iff_fg.mpr (by rw [hFHt]; exact (hfgFt.map _).sup fgK)
  have fD : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) :=
    Module.Finite.iff_fg.mpr (fgH.sup fgK)
  have hmapcD' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map
      (comp a N τ) = (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) := by
    rw [Submodule.map_sup, hKc, sup_bot_eq, hFHt, Submodule.map_comp]
  have s1 : RelLen v ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ)
      (Fil.restrictScalars (Int0 v)) m := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hD'F ?_ fF fD' m).2 ?_
    · rintro x ⟨hxF, hx0⟩
      exact Submodule.mem_sup_right ((m3 x).2 ⟨hxF, (hker' x).1 hx0⟩)
    · rw [hmapcD']; exact hm
  have s2 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hD'F (by
      rintro x ⟨hxF, hx0⟩
      exact Submodule.mem_sup_left ⟨hxF, hkerA x hx0⟩) fF fD' m).1 s1
  have hDA' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map
      (mulR a N (lin a τ)) = (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) := by
    have h0 : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ :=
      le_bot_iff.1 (hHA ▸ Submodule.map_mono inf_le_right)
    rw [Submodule.map_sup, Submodule.map_sup, h0, hHA]
  have s3 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ)
      (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)) m := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hDB ?_ fB fD m).2 ?_
    · rintro x ⟨-, hx0⟩; exact Submodule.mem_sup_left (hkerA x hx0)
    · rw [← hDA', hmapB_A]; exact s2
  have s4 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hDB (by
      rintro x ⟨hxB, hx0⟩
      obtain ⟨h, hh, f', hf', rfl⟩ := Submodule.mem_sup.1 hxB
      have hP0 : cofac a τ • (h + f') = 0 := (hker' _).1 hx0
      have hdh : d • h ∈ Fil := by
        rw [hPh h ((m1 h).1 hh)]
        have e1 : cofac a τ • h = -(cofac a τ • f') :=
          eq_neg_of_add_eq_zero_left (by rw [← smul_add]; exact hP0)
        rw [e1]; exact Fil.neg_mem (Fil.smul_mem _ hf')
      have hhF := hsat d h hd0 hdh
      exact Submodule.mem_sup_right ((m3 _).2 ⟨Fil.add_mem hhF hf', hP0⟩)) fB fD m).1 s3
  have hDc : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) =
      (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
    rw [Submodule.map_sup, hKc, sup_bot_eq]
  rw [hDc] at s4
  have s5 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hBX (by
      rintro x ⟨hxX, hx0⟩
      exact Submodule.mem_sup_right (hXker ⟨hxX, hx0⟩)) fX fB δ).1 hδ
  have s6 := GlobalTheory.T.relLen_trans_add C v _ _ _ _ δ m s4 s5
  have hrδ : r = δ + m := RelLen.unique v hlen s6
  refine ⟨δ, e₂, m, ha1, hb, he₂, hm, ?_, ?_⟩
  · rw [hsum, hfr, hjr]
  · intro hall
    have hy : yExp v a Fil τ = eigRank v a Fil τ • vd v a τ := by
      unfold yExp vd
      rw [Finset.sum_congr rfl (fun s _ => by rw [hall s]), ← Finset.smul_sum,
        addVal_prod v]
      congr 1
      exact Finset.sum_congr rfl (fun s _ => v.map_sub_swap _ _)
    have hrj : r = (eigRank v a Fil τ : ℝ) * rd := by
      have : (r : WithTop ℝ) = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ) := by
        rw [hr, hy, hjr]
      exact_mod_cast this
    have hδ0 := relLen_nonneg hδ
    have hm0 := relLen_nonneg hm
    have he0 := relLen_nonneg he₂
    rw [hfr] at hsum
    rw [hjr]
    refine ⟨hδ0, ?_, hm0, ?_⟩
    · exact WithTop.coe_le_coe.2 (by linarith)
    · exact WithTop.coe_le_coe.2 (by linarith)

/- English proof (translation)
Introduce `C _ v S _ _ a ha N Fil hsat τ r hr hlen` and use `herbrand_lengthIdentities_auxiliary_bound C v S a ha N Fil hsat τ r hr hlen`.
-/
theorem lengthIdentities_of_relLen : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → LengthIdentities v a Fil τ :=
  fun C _ v S _ _ a ha N Fil hsat τ r hr hlen =>
    herbrand_lengthIdentities_auxiliary_bound C v S a ha N Fil hsat τ r hr hlen

end GlobalTheory.HerbLen
