module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointLattice_moved_rational_isometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  first | exact @GlobalTheory.TwLatRat.lat_moved | exact GlobalTheory.TwLatRat.lat_moved | (intros; apply GlobalTheory.TwLatRat.lat_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeLocalizationCompanionLatticeEqOfLocalizatioStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeLocalization_companionLattice_eq_of_localizations : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ'.FG →
    Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ' →
    Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ' →
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  first | exact @GlobalTheory.CompanLocP.locP_companion_eq | exact GlobalTheory.CompanLocP.locP_companion_eq | (intros; apply GlobalTheory.CompanLocP.locP_companion_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RepsOfEqImage
section
noncomputable section

namespace GlobalTheory.TwU.XiTwo

section Abs

open Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison Formalism.L2.KerInert.RepComb

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [DecidableEq W]
  (H : Sesq V) (α : V → ℂ) (H₁ : Sesq W) (α₁ : W → ℂ) (T : V ≃+ W)

omit [DecidableEq W] in
theorem brk_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (y t : V) : brk H₁ (T y) (T t) = brk H y t := by
  unfold brk altE
  rw [hH]

theorem hatS_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (vol : ℝ) (SA : Finset V) (Φ : W → ℂ) (x y : V) :
    hatS H₁ vol (SA.image T) (fun s => Φ (s - T x)) (T y) = hatS H vol SA (fun s => Φ (T (s - x))) y := by
  unfold hatS
  rw [Finset.card_image_of_injective _ T.injective, Finset.sum_image (fun a _ b _ h => T.injective h)]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [brk_map H H₁ T hH]
  simp only [map_sub]

omit [DecidableEq W] in
theorem opU_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (x : V) (e : W → ℂ) (z : V) :
    opU H₁ (T x) e (T z) = opU H x (fun v => e (T v)) z := by
  unfold opU
  rw [hH, hH, ← map_add (f := _)]

theorem xiL_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (hα : ∀ x, α₁ (T x) = α x) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : W → ℂ) (z : V) :
    xiL H₁ α₁ vol (SX.image T) (SA.image T) (SB.image T) Φ e (T z) =
      xiL H α vol SX SA SB (fun v => Φ (T v)) (fun v => e (T v)) z := by
  rw [xiL_expand, xiL_expand, Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hatS_map H H₁ T hH, hα, hα, hH, hH, ← map_add (f := _), opU_map H H₁ T hH]


omit [Module ℂ V] [Module ℂ W] in
theorem isReps_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) : IsReps M₁ M₂ (S.image T) := by
  first
  | exact @_root_.GlobalTheory.RepresentativesImage.isReps_image
  | exact _root_.GlobalTheory.RepresentativesImage.isReps_image
  | (apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RepresentativesImage.isReps_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RepresentativesImage.isReps_image ..)


omit [Module ℂ V] [Module ℂ W] in
theorem repsOf_eq_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} (hS : ∃ S, IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) :
    ∃ S : Finset V, IsReps Λ₁ Λ₂ S ∧ repsOf M₁ M₂ = S.image T := by
  classical
  obtain ⟨S, hS⟩ := hS
  have hex : ∃ S₁, IsReps M₁ M₂ S₁ := ⟨_, isReps_image T hS h1 h2⟩
  have hR : IsReps M₁ M₂ (repsOf M₁ M₂) := by
    unfold repsOf
    exact Classical.epsilon_spec hex
  refine ⟨(repsOf M₁ M₂).image T.symm, isReps_image T.symm hR (fun x => ?_) (fun x => ?_), ?_⟩
  · rw [← h1, AddEquiv.apply_symm_apply]
  · rw [← h2, AddEquiv.apply_symm_apply]
  · rw [Finset.image_image]
    have : (T ∘ T.symm : W → W) = id := funext fun x => T.apply_symm_apply x
    rw [this, Finset.image_id]

end Abs

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_two : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  intro V W _ _ _ _ H α H₁ α₁ T hH hα A B Λ A₁ B₁ Λ₁ hyp hΛ hA hB hX hSA hSB vol θ Φ hθ hΦ z
  classical
  have hΛA : ∀ x, T x ∈ Λ₁ ⊓ A₁ ↔ x ∈ Λ ⊓ A := fun x => by
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, hΛ, hA]
  obtain ⟨SX, rX, eX⟩ := repsOf_eq_image T hX hΛ hA
  obtain ⟨SA, rA, eA⟩ := repsOf_eq_image T hSA hB hΛA
  obtain ⟨SB, rB, eB⟩ := repsOf_eq_image T hSB hΛ hB
  rw [eX, eA, eB, xiL_map H α H₁ α₁ T hH hα]
  exact twist_representatives V H α A B Λ hyp _ _ _ _ _ _ (GlobalTheory.TwU.KerMove.repsOf_of_exists hX) (GlobalTheory.TwU.KerMove.repsOf_of_exists hSA)
    (GlobalTheory.TwU.KerMove.repsOf_of_exists hSB) rX rA rB vol _ hθ _ hΦ z

end Main

end GlobalTheory.TwU.XiTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsCoefficientFieldFormComplexPeriodRowsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | exact GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | (intros; apply GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameCosetOfMemCosetIn
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue.Cl


open Classical in
theorem sameCoset_of_mem_cosetIn {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j)
    (h : j + 1 = R.m) (P : rowSG Pr sel mu) {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P) (hz' : z' ∈ cosetIn p P) :
    SameCoset sel mu cst P z z' := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨w', hw', hzw'⟩ := hz'
  obtain ⟨y, -, hY⟩ := p.mem_ybSet h
  rw [hY] at hw hw'
  have hww : w - w' ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    have e1 : w - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw
    have e2 : w' - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw'
    have := sub_mem e1 e2
    rwa [sub_sub_sub_cancel_right] at this
  have h1 := (mem_locLat _ _ _ _).1 hww P
  set F := frsF sel mu p.1.1 P with hF
  set c : X.E := ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ with hc
  have hc' : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ = c := by
    rw [hc]; split_ifs <;> simp
  simp only [hc'] at h1
  have hFm : ∀ x, F x ∈ p.1.1.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
    intro x
    rw [hF]
    unfold frsF
    split_ifs with hP
    · exact (Deco.liftFr_spec (Deco.Ok.hasLift p.1.1.deco.2 ⟨P.1, hP⟩)).1 x
    · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x
  have h2 : c • (F.symm w - F.symm w') ∈ stdAt X.E (R.N j) P.1 := by
    rw [← map_sub, ← map_smul]
    apply (hFm _).1
    rw [LinearEquiv.apply_symm_apply]
    exact h1
  have h3 : c • (z - z') = c • (z - F.symm w) - c • (z' - F.symm w') + c • (F.symm w - F.symm w') := by
    rw [← smul_sub, ← smul_add]
    congr 1
    abel
  have h4 : c • (z - z') ∈ stdAt X.E (R.N j) P.1 := by
    rw [h3]
    exact add_mem (sub_mem hzw hzw') h2
  intro l
  have h5 := (ciMem_stdAt _ _).1 h4 l
  rw [Pi.smul_apply, smul_eq_mul] at h5
  exact h5

end GlobalTheory.TwU.AtTrue.Cl

namespace GlobalTheory.TwU.AtTrue.Cl

end GlobalTheory.TwU.AtTrue.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroChartOfMemberLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.ZeroChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem latAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl) :
    I.latAt u a 0 (I.eCls0 l u a c) = I.latAt u I.mu0 0 c := by
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  unfold TC.latAt
  rw [dite_eq_left (Nat.zero_le _), dite_eq_left (Nat.zero_le _), e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem range_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl)
    (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) (I.eCls0 l u a c)).range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) c).range := by
  rw [Chart0.stab_range0 I hI, Chart0.stab_range0 I hI]
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  rw [e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem map_conj_mul {G : Type} [Group G] (U : Subgroup G) (y k : G) (hk : k ∈ U) :
    U.map (MulAut.conj (y * k)).toMonoidHom = U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨x, hx, hg⟩
    refine ⟨k * x * k⁻¹, (conj_mem_iff hk x).2 hx, Eq.trans ?_ hg⟩
    show y * (k * x * k⁻¹) * y⁻¹ = y * k * x * (y * k)⁻¹
    group
  · rintro ⟨x, hx, hg⟩
    refine ⟨k⁻¹ * x * k, by simpa using (conj_mem_iff (inv_mem hk) x).2 hx, Eq.trans ?_ hg⟩
    show y * k * (k⁻¹ * x * k) * (y * k)⁻¹ = y * x * y⁻¹
    group

end GlobalTheory.TwU.AtTrue.ZeroChart

end

namespace GlobalTheory.TwU.AtTrue.ZeroChart

open scoped TensorProduct


set_option maxHeartbeats 4000000 in
theorem chart_of_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u 0 (Nat.zero_le _)) (κ : (I.stp u I.mu0 0).Cl → K.lev.U), (∀ c s, (K.stabI c s).1 = (I.stp u I.mu0 0).gam c.1 s.1) → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (K0 ()).lev.Lb = K.lev.Lb ∧ (K0 ()).lev.Uloc = K.lev.Uloc ∧ (K0 ()).lev.U = K.lev.U ∧ (∀ (x : (K0 ()).lev.U) (x' : K.lev.U), x.1 = x'.1 → (K0 ()).lev.chi x = K.lev.chi x') ∧ (∀ c, ((K0 ()).y ⟨I.eCls0 l u a c, rfl⟩).1 = (K.y c).1 * (κ c).1) ∧ ∀ c s, ((K0 ()).stabI c s).1 = (I.stp u a 0).gam c.1.1 s.1 := by
  intro B X I hI hP l Z u a Q K κ hK
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  let e := I.eCls0 l u a
  have hU : ∀ c, (κ c).1 ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ((K.lev.U_eq _).1 (κ c).2).1
  let κU : ∀ c, UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ⟨(κ c).1, hU c⟩
  have hL : ∀ c, (κ c).1 ∈ levelAfL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) K.lev.Lb := fun c =>
    (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ _ _ _ _ K.lev.Lb_fin _).2
      ⟨hU c, fun v => K.lev.Uloc_lev v (((K.lev.U_eq _).1 (κ c).2).2 v)⟩
  have hlat : ∀ c'', I.latAt u a 0 c'' = I.latAt u I.mu0 0 (e.symm c'') := by
    intro c''
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact latAt_eCls0 I hI l u a c
  have hrng : ∀ c'' (γ : GL (Fin (B.R.N 0)) B.host.E),
      γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'').range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) (e.symm c'')).range := by
    intro c'' γ
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact range_eCls0 I hI l u a c γ
  have hmem : ∀ c'' (s : (I.stp u a 0).Stab c''),
      MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'' s ∈
        UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi) := by
    intro c'' s
    obtain ⟨t, ht⟩ := (hrng c'' _).1 ⟨s, rfl⟩
    rw [← ht]
    exact (congrArg (fun g => g ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi))
      (hK (e.symm c'') t)).mp (K.stabI (e.symm c'') t).2
  have hcls : ∀ c, (Quotient.mk'' (K.y c * κU c) : Cls K.lev) = Quotient.mk'' (K.y c) := fun c => by
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨1, one_mem _, (κU c)⁻¹, ?_, by group⟩
    exact inv_mem (κ c).2
  refine ⟨fun _ =>
    { lev :=
        { K.lev with
          Uloc_hyp := fun v hv hT => K.lev.Uloc_hyp v (fun h => hv (Or.inl h)) hT
          chi_triv := fun x hx => K.lev.chi_triv x (fun v hv => hx v (Or.inl hv)) }
      y := fun c' => K.y (e.symm c'.1) * κU (e.symm c'.1)
      y_bij := ?_
      y_lat := ?_
      stabI := fun c' => (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)
      stabI_inj := fun c' s t h => MemChart.stM_inj (Chart0.lvG I a) (Chart0.lvQ I a) _ _ ((l.ch u a).step 0) c'.1 (congrArg Subtype.val h)
      stabI_range := ?_ }, rfl, rfl, rfl, fun x x' h => ?_, fun c => ?_, fun c s => rfl⟩
  · convert K.y_bij.comp (e.symm.bijective.comp
        (Equiv.subtypeUnivEquiv (p := fun c' : (I.stp u a 0).Cl => (fun _ => ()) c' = ()) (fun _ => rfl)).bijective) using 1
    funext c'
    exact hcls (e.symm c'.1)
  · intro c' x
    rw [hlat c'.1]
    refine (K.y_lat (e.symm c'.1) x).trans ?_
    show _ ↔ ((((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)⁻¹).1 *ᵥ x ∈ _)
    have hm : ∀ (g h : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N 0)) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] FiniteAdeleRing (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)),
        ((g * h)⁻¹).1 *ᵥ x = (h⁻¹).1 *ᵥ ((g⁻¹).1 *ᵥ x) := by
      intro g h
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    rw [hm (K.y (e.symm c'.1)).1 (κ (e.symm c'.1)).1]
    exact (inv_mem (hL _)).2 _
  · intro c' γ
    have h1 : γ ∈ ((MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)).range ↔
        γ.1 ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).range :=
      ⟨fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩, fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩⟩
    refine h1.trans ((hrng c'.1 γ.1).trans (Iff.trans ?_ ((K.stabI_range (e.symm c'.1) γ).trans ?_)))
    · exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext ((hK _ t).trans ht)⟩, fun ⟨t, ht⟩ => ⟨t, (hK _ t).symm.trans (congrArg Subtype.val ht)⟩⟩
    show _ ↔ _ ∈ K.lev.U.map (MulAut.conj ((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)).toMonoidHom
    rw [map_conj_mul _ _ _ (κ _).2]
  · show K.lev.chi x = K.lev.chi x'
    exact congrArg K.lev.chi (Subtype.ext h)
  · show (K.y (e.symm (e c))).1 * (κ (e.symm (e c))).1 = _
    rw [e.symm_apply_apply]

end GlobalTheory.TwU.AtTrue.ZeroChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroFormIdentificationRefTupleEqId
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem stepZeroFormIdentification_refTuple_eq_id : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word), (I.tw l l0 Z).e0 u (I.rec7 l Z).what₂.mu0 = (I.tw l l0 Z).eMu0 u 0 (Nat.zero_le _) := by
  intro B X I _ _ l Z l0 u
  apply LinearEquiv.ext
  intro x
  have h := (l0 u I.mu0).choose_spec.2 x
  rw [stepZeroTwist_reference_tuple_eq_id l u] at h
  exact (I.fm l u I.mu0).emb_inj 0 h

end GlobalTheory.TwU.AtTrue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelCharacterEqReferenceTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.StepZeroChr

theorem isPtOf_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩


set_option maxHeartbeats 1000000 in
theorem chr_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → chi κ0 = 1 → ∀ (x : U) (κ : (I.stp u a 0).G c'.1), (I.stp u a 0).gam c'.1 κ = 1 → PtOf (y c * κ0.1 * x.1 * k) ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 → ((chi x : ℂˣ) : ℂ) = B.embLL (((I.stp u a 0).chr c'.1 κ : B.LLˣ) : B.LL) := by
  intro B X I hI hP l Z u a Lb U chi y st k hR c κ0 c' hc' _ hchi x κ hκ hpt
  have hd : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    subst hc'
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  have hΛ := ClsZero.levelTypePrimes_stepZero_eq_colLev hI a c'.1
  have hΛ0 := ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 c.1
  have hm : κ.2.1.1 ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).grp := by
    rw [hΛ0, ← hΛ]
    exact κ.2.1.2
  let κ' : (I.stp u I.mu0 0).G c.1 := (κ.1, ⟨κ.2.1.1, hm⟩, 1)
  have e1 : ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1.deco =
      ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1.deco := by
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u I.mu0 0).rep c).1.1.deco = ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u a 0).rep c').1.1.deco
    rw [hd]
  have h1 : PtOf (y c * (κ0 * x).1 * k) ((I.stp u I.mu0 0).act c.1 κ' ((I.stp u I.mu0 0).rep c)).1.1 := by
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact isPtOf_of_deco (RefTup.twistPrimes_reference_tuple_eq_empty B X I) e1 hpt
  have h2 := hR.chr c (κ0 * x) κ' hκ h1
  rw [map_mul, hchi, one_mul] at h2
  refine h2.trans ?_
  congr 2
  show (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr ⟨κ.2.1.1, hm⟩ *
      (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr 1 =
    (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 c'.1).chr κ.2.2
  rw [map_one, StepZero.chr_eq_one (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a c'.1), StepZero.chr_congr hΛ, StepZero.chr_congr hΛ0]

end GlobalTheory.TwU.StepZeroChr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelReadAsReference
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevZero

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem moves_iff (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) :
    (∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c)) ↔
      ∃ g : FormG (colLev I.Ch 0), ufGL B.fields.E (B.R.N 0) g.1 = 1 ∧ g • ((I.stp u a 0).rep c).1.1.deco = q.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  constructor
  · rintro ⟨κ, h1, h2, -⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) ((I.Tp a).pref u 0) hΛ c.1 κ, h1, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := Chart0.lvQ I a) _ hΛ c.1 κ _).symm.trans
      (congrArg (fun q => q.deco) h2)
  · rintro ⟨g₀, h0, hg⟩
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p g₀ (by rw [hp]; exact hg)
    refine ⟨g, ?_, ?_, Chart0.cos0 I _ _⟩
    · exact (congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h2).trans h0
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp

theorem lev_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)) (U : Subgroup (GA B (B.R.N 0))) (chi : U →* ℂˣ) (y : (I.stp u I.mu0 0).Cl → GA B (B.R.N 0)) (st : ∀ c, (I.stp u I.mu0 0).Stab c → GL (Fin (B.R.N 0)) B.host.E) (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st (fun _ => k) → ∀ (c : (I.stp u I.mu0 0).Cl) (κ0 : U) (c' : (I.stp u a 0).Cl), c' = I.eCls0 l u a c → PtOf (y c * κ0.1 * k) (extTo I.SQ ((I.stp u a 0).rep c').1.1) → ∀ (x : GA B (B.R.N 0)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0), PtOf (y c * κ0.1 * x * k) q → (x ∈ U ↔ ∃ κ : (I.stp u a 0).G c'.1, (I.stp u a 0).gam c'.1 κ = 1 ∧ ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')).1.1 = q ∧ cosetIn ((I.stp u a 0).act c'.1 κ ((I.stp u a 0).rep c')) = cosetIn ((I.stp u a 0).rep c')) := by
  intro B X I hI _ l _ u a Lb U chi y st k hR c κ0 c' hc' _ x q hq
  have hQ : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hq0 : PtOf (y c * (κ0.1 * x) * k) (extTo (I.Q I.mu0) q) := by
    rw [← mul_assoc]
    exact IsPtOf.extTo (hQ ▸ Finset.empty_subset _) (hQ ▸ Finset.disjoint_empty_right _) hq
  have h1 := hR.lev c (κ0.1 * x) (extTo (I.Q I.mu0) q) hq0
  have e : ((I.stp u a 0).rep c').1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
    rw [hc']
    exact ClsZero.stepZero_corresponding_representatives_same_deco hI u a _ c
  refine (Subgroup.mul_mem_cancel_left U κ0.2).symm.trans (h1.trans ((moves_iff I hI u I.mu0 c _).trans ?_))
  refine Iff.trans ?_ (moves_iff I hI u a c' q).symm
  rw [e]
  rfl

end GlobalTheory.Mem.Col2.TC.LevZero

end
end

