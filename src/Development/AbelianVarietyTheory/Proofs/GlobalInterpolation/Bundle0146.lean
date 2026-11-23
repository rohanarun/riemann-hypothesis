module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeightsranchOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitarySplit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU (E := E) (n := n) :=
  ((((finGL E n).comp (GeneralLinearGroup.map (pFin E))).comp (UA E n).subtype).codRestrict (UA E n)
    fun g => GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)).codRestrict (finU (E := E) (n := n))
    fun _ => pInf_finGL _

def infPart : UA E n →* infU E n :=
  (((infGL E n).comp cInf).codRestrict (UA E n)
    fun g => by
      have h := (UA E n).mul_mem g.2 ((UA E n).inv_mem (finPart g).1.2)
      have e : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl
      rw [e] at h
      nth_rewrite 1 [← infGL_mul_finGL g.1] at h
      rw [mul_inv_cancel_right] at h
      exact h).codRestrict (infU E n)
    fun _ => pFin_infGL _

theorem finPart_val (g : UA E n) : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl

theorem infPart_val (g : UA E n) : (infPart g).1.1 = infGL E n (GeneralLinearGroup.map (pInf E) g.1) := rfl

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.ClassFin.continuous_finGL.comp
    ((Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
      continuous_subtype_val)

theorem continuous_infPart : Continuous (infPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.continuous_infGL.comp GlobalTheory.DefU.continuous_cInf

theorem finPart_mul_infPart (g : UA E n) : g = (finPart g).1 * (infPart g).1 := by
  rw [GlobalTheory.DefU.fin_mul_inf (finPart g).2 (infPart g).2]
  exact Subtype.ext (infGL_mul_finGL g.1).symm

theorem cInf_infPart (g : UA E n) : cInf (infPart g).1 = cInf g := pInf_infGL _

theorem finPart_fin (g : finU (E := E) (n := n)) : finPart g.1 = g :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext ((pInf_finGL _).trans g.2.symm) (pFin_finGL _)))

theorem infPart_inf (k : infU E n) : infPart k.1 = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext (pInf_infGL _) ((pFin_infGL _).trans k.2.symm)))

theorem finPart_inf (k : infU E n) : finPart k.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pFin E) k.1.1 = 1 := k.2
  rw [finPart_val, h, map_one]
  rfl

theorem infPart_fin (g : finU (E := E) (n := n)) : infPart g.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pInf E) g.1.1 = 1 := g.2
  rw [infPart_val, h, map_one]
  rfl

theorem dense_rat_inf : Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} := by
  intro k
  rw [← infPart_inf k]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPart
    ⟨k.1, GlobalTheory.WeightRealExt.dense_rat_fin k.1, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, g, hg, rfl⟩, rfl⟩
  refine ⟨γ, hγ, ?_⟩
  have hg' : cInf g = 1 := hg
  rw [cInf_infPart, map_mul, hg', mul_one]

theorem dense_and_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU (E := E) (n := n), k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU (E := E) (n := n)) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  intro E _ _ _ n
  refine ⟨GlobalTheory.WeightRealExt.dense_rat_fin, dense_rat_inf, fun k g hg => (GlobalTheory.DefU.fin_mul_inf hg k.2).symm,
    finPart, infPart, continuous_finPart, continuous_infPart, finPart_mul_infPart, fun g k => ⟨?_, ?_⟩⟩
  · rw [map_mul, finPart_fin, finPart_inf, mul_one]
  · rw [map_mul, infPart_fin, infPart_inf, one_mul]

end GlobalTheory.UnitarySplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignature
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate
attribute [local instance] IsCMField.starRing

namespace GlobalTheory.SelfDualDet
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy GlobalTheory.LocalLattice

theorem congr_of_hasSignature {r p q : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ Bᵀ = Qᵀ * Aᵀ * Q.map conj := by
  obtain ⟨e, P, hP⟩ := hA
  obtain ⟨f, R, hR⟩ := hB
  have hc : ∀ M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ :=
    fun _ => rfl
  rw [hc] at hP hR
  have h1 : Matrix.reindex f f B = (P * R⁻¹).1ᴴ * Matrix.reindex e e A * (P * R⁻¹).1 := by
    have h2 : (R⁻¹).1ᴴ * R.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    calc Matrix.reindex f f B = ((R⁻¹).1ᴴ * R.1ᴴ) * Matrix.reindex f f B * (R.1 * (R⁻¹).1) := by
          rw [h2, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (R⁻¹).1ᴴ * (R.1ᴴ * Matrix.reindex f f B * R.1) * (R⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hR, ← hP, Units.val_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  generalize P * R⁻¹ = S at h1
  refine ⟨S.1.submatrix e f, ?_, ?_⟩
  · refine (Matrix.isUnit_det_of_right_inverse (B := (S⁻¹).1.submatrix f e) ?_).ne_zero
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  · have h3 := congrArg (fun M => (Matrix.submatrix M f f)ᵀ) h1
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] at h3
    rw [← Matrix.submatrix_mul_equiv _ _ f e f, ← Matrix.submatrix_mul_equiv _ _ f e e,
      Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] at h3
    exact h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_eq_of_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {r r' : ℕ} (h : r = r')
    {G : Matrix (Fin r) (Fin r) E} {G' : Matrix (Fin r') (Fin r') E}
    (hG : ∀ a b, cc (Gᵀ a b) = Gᵀ b a) (hG' : ∀ a b, cc (G'ᵀ a b) = G'ᵀ b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} {L' : Submodule (𝓞 E) (Fin r' → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm G'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) :
    ∃ z : E, G'.det = z * star z * G.det := by
  subst h
  obtain ⟨P, -, hP⟩ := congr_of_modular (E := E) (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun _ hz => mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hz)))
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd)
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd')
    fun τ => by
      obtain ⟨p, q, h1, h2⟩ := hs τ
      exact congr_of_hasSignature h1 h2
  have h1 := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_transpose,
    Published.det_map_cc] at h1
  refine ⟨P.det, h1.trans ?_⟩
  change _ = _ * cc _ * _
  ring

theorem det_eq_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  intro E _ _ _ hc W₁ W₂ h₁ h₂ hr hs
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  exact det_eq_of_matrix hr (fun a b => W₁.herm.eq (W₁.frame b) (W₁.frame a))
    (fun a b => W₂.herm.eq (W₂.frame b) (W₂.frame a))
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₂).ne_zero
    (isLattice_coordLat W₁ W₁.L0 W₁.standardTuple_isLattice W₁.baseLattice_isUnimodular)
    (isLattice_coordLat W₂ W₂.L0 W₂.standardTuple_isLattice W₂.baseLattice_isUnimodular)
    (selfDual_coordLat W₁ W₁.L0 W₁.baseLattice_isUnimodular) (selfDual_coordLat W₂ W₂.L0 W₂.baseLattice_isUnimodular)
    fun τ => ⟨_, _, h₁ τ, hs τ ▸ h₂ τ⟩

end GlobalTheory.SelfDualDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvaluationMapTrueChainFormsToFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluationMap_trueChain_forms_to_forms :
    ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I →
      ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (l0 : TC.Law0 I l)
        (u : B.Word) (a : I.ι),
        (∀ φ ∈ ((TC.tw I l l0 Z).fm u a).Fi B.R.m,
          GlobalTheory.PerQ.PtT (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u a φ ∈
            ((TC.tw I l l0 Z).fm u a).ptC) ∧
        ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).fm u).SgInterlace := by
  intro B X I _ l Z l0 u a
  have hs : ∀ τ, (TC.perIn I u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hW := GlobalTheory.LvT.BuiltChain.weights_ok (TC.perIn I u a) (B.hcW u) B.fields.emb hs
  refine ⟨?_, ?_⟩
  · intro φ hφ
    let M := TC.fm I l u a
    have latticeImage : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x hx
      obtain ⟨y, -, hy⟩ := GlobalTheory.LvT.BuiltChain.exists_image (Q := TC.perIn I u a)
        B.fields.emb B.embLL (B.hcW u) GlobalTheory.LvT.BuiltChain.branching_ok
        (l.ch u a) (l.per u a) (fun τ => (hW τ).1) (fun τ => (hW τ).2)
        ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx
      exact ⟨y, hy⟩
    have rationalImage : ∀ x, ∃ y, M.ptEmb y =
        (TC.per I l u a).lowerMap ((TC.per I l u a).evz (M.emb B.R.m x)) := by
      intro x
      have hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V) := by
        rw [(M.lat_good B.R.m).2.2]
        trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact latticeImage x hx
      | zero => exact ⟨0, by simp⟩
      | add x x' _ _ hx hx' =>
        obtain ⟨y, hy⟩ := hx
        obtain ⟨y', hy'⟩ := hx'
        exact ⟨y + y', by rw [map_add, map_add, map_add, map_add, hy, hy']⟩
      | smul r x _ hx =>
        obtain ⟨y, hy⟩ := hx
        refine ⟨r • y, ?_⟩
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hy, LinearMap.map_smul, LinearMap.map_smul]
    have ptMem : ∀ y, M.ptEmb y ∈ M.ptC := by
      intro y
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
    have hφ' : φ ∈ M.Fi B.R.m := hφ
    rw [← (M.emb_basis B.R.m).2] at hφ'
    have hle : Submodule.span ℂ (Set.range fun c => M.emb B.R.m ((M.lat B.R.m).b c)) ≤
        M.ptC.comap ((TC.per I l u a).lowerMap ∘ₗ (TC.per I l u a).evz) := by
      rw [Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      obtain ⟨y, hy⟩ := rationalImage ((M.lat B.R.m).b c)
      show (TC.per I l u a).lowerMap ((TC.per I l u a).evz _) ∈ M.ptC
      rw [← hy]
      exact ptMem y
    exact hle hφ'
  · intro τ i
    obtain ⟨ha, hb⟩ := (hW τ).1 i
    simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT,
      GlobalTheory.Mem.Col2.shW] at ha hb
    constructor
    · show (B.wts.sgW τ).w i ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩
      change 0 ≤ (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ).w i + _) at hb
      linarith
    · show (Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ).w i
      change 0 ≤ (B.wts.sgW τ).w i + _ - ((Examples₂.lamOf (B.hcW u τ) B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
      linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralHyperplaneFormOfLocalCoordsIntegra
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co.PtInt

theorem natW_sgT {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (τ : B.fields.Tau) :
    ((I.perIn u a).sgT τ).natW = ((I.perIn u a).sg τ).natW := by
  funext i
  simp only [DomWeight.natW, PerIn.sgT, Col2.shW, DomWeight.detShift]
  split_ifs with h
  · congr 1
    ring
  · exact absurd i.2 (by omega)

theorem invTrK_bc {E K ι : Type} [Field E] [Field K] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (γ : GL (Fin n) E) :
    (fun τ => Formalism.UG.bc σ (invTrK (embGL emb γ) τ)) = invTrK (embGL (embAt σ emb) γ) := by
  funext τ
  ext a b
  have h1 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply emb γ τ a b
  have h2 := GlobalTheory.LvT.BuiltChain.invTrK_embGL_apply (embAt σ emb) γ τ a b
  rw [h2]
  show σ (((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) = _
  rw [h1]
  rfl

end GlobalTheory.PerQ.Co.PtInt

theorem GlobalTheory.PerQ.Co.PtInt.exists_mem_SP_of_coP_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg) → ∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z := by
  intro B X I hI l Z l0 u a w z hz hco
  have hOk : (I.perIn u a).S'.Ok := (l.per u a).step
  have hz' : z ∈ (I.perIn u a).S'.Fi B.fields.emb B.embLL (I.perIn u a).sgT := hz
  have key : ∀ c : (I.perIn u a).S'.Cl, ∃ v : Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT,
      z c = evV B.fields.emb (1 : Matrix _ _ B.fields.E) (I.perIn u a).sgT B.embLL v ∧
      v ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    intro c
    obtain ⟨P, hP, hPz⟩ := (hz' c).1
    obtain ⟨G, hG, hGe⟩ := (GlobalTheory.LvT.Built.ValLat.mem_intSpan_iff (I.rec7 l Z) w _ (I.perIn u a).sgT
      (fun τ => (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a τ).symm) _).1 (hco c)
    have hGV : G ∈ Formalism.L2.DIV.VV B.fields.K (I.perIn u a).sgT := GlobalTheory.LvT.Built.ValLat.mem_VV_of_locP _ _ hG
    have hspec := _root_.GlobalTheory.PerQ.Co.usage₉ I hI l u a w c
    refine ⟨rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩, ?_, ?_⟩
    · rw [← hPz]
      show fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1 P =
        fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          (MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1)
      congr 1
      have e1 : (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩).1 =
          actP (I.perIn u a).sgT (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G := rfl
      rw [e1]
      have e3 := GlobalTheory.LvT.Built.ValLat.map_actP B.embLL (I.perIn u a).sgT
        (invTrK (embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c))) G
      rw [GlobalTheory.PerQ.Co.PtInt.invTrK_bc] at e3
      refine Eq.trans ?_ e3.symm
      refine Eq.trans ?_ (congrArg (actP (I.perIn u a).sgT
        (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))) hGe)
      show P = actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)))
        (actP (I.perIn u a).sgT (invTrK (embGL (embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
          (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
            (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (z c)))
      rw [← polyAction_mul, map_inv, map_inv, mul_inv_cancel, polyAction_one₂, ← hPz]
      have h := polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT)
        (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) P
      have e : (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
      rw [e] at h
      exact h.symm
    · have hinv : rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹
          (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c) ⟨G, hGV⟩) = ⟨G, hGV⟩ := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [_root_.GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).sgT
        (I.perIn u a).sg (GlobalTheory.PerQ.Co.PtInt.natW_sgT I u a) _ (hOk.lsh_full_lat c.1 _) w _ hspec.1, hinv]
      have h := hco c
      rw [hGe] at h
      exact h
  choose v hv1 hv2 using key
  obtain ⟨y, hy1, hy2⟩ := _root_.GlobalTheory.Glob.FormDescent.desc B.fields.emb B.embLL (I.perIn u a).S' (I.perIn u a).sgT (l.fmL u a).famP z hz' v hv1
  refine ⟨y, ?_, hy2⟩
  show y ∈ locW B.places w ((I.perIn u a).S'.hlat B.fields.emb (I.perIn u a).sgT (l.fmL u a).famP).L
  rw [_root_.GlobalTheory.Mem.Col2.mem_locW_hlat_iff B.fields.emb B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq (I.perIn u a).S' (I.perIn u a).sgT
    (l.fmL u a).famP hOk w y]
  intro c
  rw [hy1 c]
  exact hv2 c
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HyperplaneFormIntegralLocalCoordsMemIntegralSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtIntCoord

theorem natW_shW {n : ℕ} (l : DomWeight n) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  have e : GlobalTheory.Mem.Col2.shW l c = Formalism.MainNotions.product_first_zeroth_parts.wSh l (-c) := by
    unfold GlobalTheory.Mem.Col2.shW Formalism.MainNotions.product_first_zeroth_parts.wSh
    congr 1
    funext i
    ring
  rw [e, Formalism.MainNotions.product_first_zeroth_parts.natW_wSh]

theorem coP_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z) → ∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg := by
  intro B X I hI l Z l0 u a w z _hz hyz c
  obtain ⟨y, hy, rfl⟩ := hyz
  clear _hz
  have hQ : (I.perIn u a).Ok := l.per u a
  have hA : y.1 c ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT
      ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hx c)
    | zero => exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => exact Submodule.add_mem _ hx hx'
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hB := (_root_.GlobalTheory.PerQ.Co.usage₉ I hI l u a w c).1
  have key := (_root_.GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (I.perIn u a).sgT (I.perIn u a).sg (fun τ => natW_shW _ _) _ (hQ.step.lsh_full_lat c.1 _) w _ hB (y.1 c)).1 hA
  have e : GlobalTheory.PerQ.Co.coP I u a w (((I.tw l l0 Z).fm u a).ptEmb y) c =
      MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹ (y.1 c)).1 := by
    show actP _ _ (polOf _ _ _ (evV B.fields.emb 1 (I.perIn u a).sgT B.embLL (y.1 c))) = _
    rw [GlobalTheory.LvT.BuiltChain.polOf_evV]
    show _ = MvPolynomial.map B.embLL (actP (I.perIn u a).sgT
      (invTrK (Formalism.L2.DIV.embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹)) (y.1 c).1)
    rw [GlobalTheory.ValCmp.use₂]
    congr 2
  rw [e]
  exact key

end GlobalTheory.PtIntCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCoordsEvaluationLowerRowMapEqTensorBranchin
section
noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem coP_PtT_eq_blk : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi (I.rec7 l Z).R.m, ∀ c, GlobalTheory.PerQ.Co.coP I u a w (GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ) c = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)) (GlobalTheory.PerQ.Co.coM I u a w c (φ (((I.tw l l0 Z).fm u a).til c))) := by
  intro B X I hI l Z l0 u a w φ hφ c
  have hV : φ ((I.perIn u a).tilC c) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) := (hφ _).1
  have hT : ((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) :=
    GlobalTheory.LvT.Built.RealM.trFr_mem _ _ _ _ _ hV
  obtain ⟨F, hF⟩ := (GlobalTheory.TilClass.mem_ValC_iff _ _ _ _).1 hT
  have hW := fun τ => _root_.GlobalTheory.PerQ.trueWeights_built I hI l Z u a τ
  have hS := _root_.GlobalTheory.PerQ.Co.usage₉ I hI l u a w c
  show actP (I.perIn u a).sgT (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1))
        (fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          ((I.perIn u a).br B.fields.emb B.embLL (B.hcW u)
            (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
              (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c))))))) =
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
      (actP (lamT (B.hcW u) B.R.m) (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
          (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)))))

  rw [← hF, GlobalTheory.TilClass.polOf_fnOf_one, GlobalTheory.TilClass.polOf_fnOf_one]
  have hlam : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = lamT (B.hcW u) B.R.m := funext fun τ => (hW τ).1
  have hsg : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = (I.perIn u a).sgT := funext fun τ => (hW τ).2.1
  refine Eq.trans ?_ (GlobalTheory.Proof.FockBlockMonotone.blk_brOne_eq (ι := B.fields.Tau) (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm _ _ _).symm
  rw [hlam, hsg]
  have key := GlobalTheory.BranchBlock.rhoVr_brAt_eq_brStd (embAt B.embLL B.fields.emb) (N_m_succ B.R) (lamT (B.hcW u) B.R.m)
    (I.perIn u a).sgT (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) (I.perIn u a).tz _ _ hS.2.1 hS.2.2.1 F
  exact congrArg Subtype.val key

end GlobalTheory.PerQ.Co

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RightFiniteMemPoly
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem rightFinite_mem_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (f : infU E n → ℂ), Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n => f (x * k))) → f ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} := by
  intro E _ _ _ n f hf hfin
  haveI := _root_.GlobalTheory.InfUCompact.compactSpace_infU E n
  obtain ⟨hc, hs, hsep, hinv, hcop⟩ := _root_.GlobalTheory.PolyRealU.poly_infU E n
  haveI : T2Space (infU E n) := ⟨fun x y hxy => by
    obtain ⟨p, hp, hne⟩ := hsep x y hxy
    exact separated_by_continuous (hc p hp) hne⟩
  refine _root_.GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates (infU E n) (Algebra.adjoin ℂ _) hc hs hsep ?_ f hf hfin
  intro p hp
  obtain ⟨m, a, b, hab, heq⟩ := hcop p hp
  refine ⟨m, fun i x => a i x⁻¹, b, fun i => ⟨hinv _ (hab i).1, hc _ (hab i).2⟩, ?_⟩
  intro x k
  exact heq x⁻¹ k

end GlobalTheory.UnitaryBC
end

