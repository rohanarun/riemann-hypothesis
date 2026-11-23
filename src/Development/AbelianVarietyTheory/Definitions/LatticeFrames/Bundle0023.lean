module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.LocalToGlobal.HermitianForms.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NonemptyOffDatOfTrueD
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffInh

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

attribute [local instance] GlobalTheory.FinPl.Model.relAt GlobalTheory.FinPl.Model.locAt

section Empty

variable {P : Pl D → Prop}

theorem mem_GinfC_of_all (hP : ∀ v, P v) {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) : g ∈ GinfC S := by
  rw [grpOff, congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff] at hg
  rw [GinfC, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  intro i j
  have e : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
      (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have h1 : Formalism.L2.Theta.mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P :=
    Ideal.Quotient.eq.1 ((hg i j).trans e.symm)
  have h2 := GlobalTheory.SelfDualAt.eq_zero_of_compFin (finPart D _) fun w => (Submodule.mem_iInf _).1 h1 ⟨w, hP w⟩
  rw [RingHom.map_sub, sub_eq_zero] at h2
  refine h2.trans ?_
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end Empty

end GlobalTheory.FinPl.OffInh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ReflectionBoostMatrixConjTransposeMulSelf
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitHalf

section Gen
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

theorem exists_inv (Φ : SB X) (A : AddSubgroup X) (hA : IsCompact (A : Set X)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a ∈ A, ∀ x, Φ.1 (x + N • a) = Φ.1 x := by
  let V : AddSubgroup X :=
    { carrier := {v | ∀ x, Φ.1 (x + v) = Φ.1 x}
      zero_mem' := fun x => by rw [add_zero]
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a), neg_add_cancel_right] }
  have key : ∀ᶠ v in 𝓝 (0 : X), ∀ x ∈ tsupport Φ.1, Φ.1 (x + v) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually Φ.2.2 fun x _ => ?_
    have h1 : IsLocallyConstant fun p : X × X => (Φ.1 (p.2 + p.1), Φ.1 p.2) :=
      (Φ.2.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk (Φ.2.1.comp_continuous continuous_snd)
    filter_upwards [h1.eventually_eq (0, x)] with p hp
    rw [Prod.mk.injEq, add_zero] at hp
    rw [hp.1, hp.2]
  have key' : ∀ᶠ v in 𝓝 (0 : X), ∀ x ∈ tsupport Φ.1, Φ.1 (x + -v) = Φ.1 x :=
    (continuous_neg.tendsto' (0 : X) 0 neg_zero).eventually key
  have hV : IsOpen (V : Set X) := by
    refine V.isOpen_of_mem_nhds (g := 0) ?_
    filter_upwards [key, key'] with v h1 h2 x
    by_cases hx : x ∈ tsupport Φ.1
    · exact h1 x hx
    · by_cases hv : x + v ∈ tsupport Φ.1
      · rw [← h2 _ hv, add_neg_cancel_right]
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hv]
  haveI : DiscreteTopology (X ⧸ V) := QuotientAddGroup.discreteTopology hV
  have hfin : ((A.map (QuotientAddGroup.mk' V) : AddSubgroup (X ⧸ V)) : Set (X ⧸ V)).Finite := by
    rw [AddSubgroup.coe_map]
    exact (hA.image QuotientAddGroup.continuous_mk).finite_of_discrete
  haveI : Finite (A.map (QuotientAddGroup.mk' V)) := hfin
  refine ⟨Nat.card (A.map (QuotientAddGroup.mk' V)), Nat.card_pos, fun a ha => ?_⟩
  have h := card_nsmul_eq_zero' (x := (⟨QuotientAddGroup.mk' V a, a, ha, rfl⟩ : A.map (QuotientAddGroup.mk' V)))
  have h2 := congrArg Subtype.val h
  simp only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero, ← map_nsmul] at h2
  exact (QuotientAddGroup.eq_zero_iff _).1 h2

theorem exists_supp {K : Set X} (hK : IsCompact K) (A : AddSubgroup X) (hA : IsOpen (A : Set X))
    (h : ∀ x, ∃ n : ℕ, 0 < n ∧ n • x ∈ A) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, N • x ∈ A := by
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun n : ℕ+ => {x | (n : ℕ) • x ∈ A})
    (fun n => hA.preimage (continuous_nsmul _)) fun x _ => by
      obtain ⟨n, hn, hx⟩ := h x
      exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hx⟩
  refine ⟨∏ n ∈ s, (n : ℕ), Finset.prod_pos fun n _ => n.pos, fun x hx => ?_⟩
  obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.1 (hs hx)
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun n : ℕ+ => (n : ℕ)) hn
  rw [hm, mul_nsmul]
  exact nsmul_mem hx _

end Gen

variable {D : D7}

theorem chart_one {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) : π e = 1 := by
  have : π (e - 1) = 0 := (hπ.2.1 _).2 (by rw [mul_sub, h1, mul_one, sub_self])
  rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this

theorem single_add {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    singleV F v (a + b) = singleV F v a + singleV F v b := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (singleV F v (a + b)) = evalV F w (singleV F v a + singleV F v b)
  by_cases hw : w = v
  · subst hw
    rw [map_add (f := _), GlobalTheory.SplitCoord.evalV_single, GlobalTheory.SplitCoord.evalV_single, GlobalTheory.SplitCoord.evalV_single]
  · rw [map_add (f := _), GlobalTheory.SplitCoord.evalV_single_ne hw, GlobalTheory.SplitCoord.evalV_single_ne hw,
      GlobalTheory.SplitCoord.evalV_single_ne hw, add_zero]

def sec (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Fv D.host.F v →+ AE D :=
  AddMonoidHom.mk' (fun a => e * algebraMap (AF D.host.F) _ (pairA D.host.F 0 (singleV D.host.F v a))) fun a b => by
    rw [← mul_add, ← RingHom.map_add (f := _), single_add]
    congr 2
    exact Prod.ext (add_zero _).symm rfl

theorem sec_cont (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) : Continuous (sec e v) := by
  have ha : Continuous (Algebra.linearMap (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hb : Continuous fun a => pairA D.host.F 0 (singleV D.host.F v a) :=
    Continuous.prodMk continuous_const (GlobalTheory.LocalComponentChar.continuous_singleV D.host.F v)
  exact continuous_const.mul (ha.comp hb)

theorem chart_sec {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) (a) : π (sec e v a) = a := by
  change π (e * algebraMap (AF D.host.F) _ (pairA D.host.F 0 (singleV D.host.F v a))) = a
  rw [RingHom.map_mul, chart_one h1 hπ, one_mul, hπ.2.2.1]
  exact GlobalTheory.SplitCoord.evalV_single v a

theorem sec_chart {e : AE D} (h1 : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {π : AE D →+* Fv D.host.F v} (hπ : GlobalTheory.SplitHecke.Chart e v π) (x) : sec e v (π x) = e * x := by
  have := (hπ.2.1 (sec e v (π x) - x)).1 (by rw [RingHom.map_sub, chart_sec h1 hπ, sub_self])
  rw [mul_sub, sub_eq_zero] at this
  rw [← this]
  change e * _ = e * (e * _)
  rw [← mul_assoc, h1]

theorem isCompact_half {e : AE D} (he : IsSplitIdem D e) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    IsCompact {t : WO S T | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t} := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  have h : IsCompact ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) := by
    first
    | exact (GlobalTheory.PlaceCoord.isOpen_isCompact_map hS hT hπ he.1 (chart_one he.1 hπ)
        (GlobalTheory.PlaceCoord.infPart_split he)).2
    | exact (GlobalTheory.PlaceCoord.isOpen_isCompact_map hS.1 hT.1 hπ he.1 (chart_one he.1 hπ)
        (GlobalTheory.PlaceCoord.infPart_split he)).2
  have hc : Continuous fun y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) => (y.map (sec e v) : WO S T) :=
    continuous_id.matrix_map (sec_cont e v)
  have h2 := h.image hc
  rw [Set.image_image] at h2
  convert h2 using 1
  refine (Set.EqOn.image_eq_self fun t ht => ?_).symm
  ext i j
  exact (sec_chart he.1 hπ _).trans (ht.2 i j)

variable {S : HSp D}

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] {n : ℕ} (e e' f : R) (G Gi a a' b b' : Matrix (Fin n) (Fin n) R) (h1 : e * e = e)
    (h1' : e' * e' = e') (h2 : e * e' = 0) (hf : f = 1 - e - e') (hba : b * a = e • (1 : Matrix (Fin n) (Fin n) R))
    (hab' : a' * b' = e' • (1 : Matrix (Fin n) (Fin n) R)) (g1 : ∀ x : Matrix (Fin n) (Fin n) R, Gi * (G * x) = x)
    (g2 : ∀ x : Matrix (Fin n) (Fin n) R, G * (Gi * x) = x) :
    (e' • a' + e • (G * b * Gi) + f • 1) * (G * (e • a + e' • (Gi * (b' * G)) + f • 1)) = G := by
  have z1 : e' * e = 0 := by rw [mul_comm, h2]
  have z2 : e' * f = 0 := by rw [hf]; linear_combination -h1' - h2
  have z3 : e * f = 0 := by rw [hf]; linear_combination -h1 - h2
  have z4 : f * e = 0 := by rw [mul_comm, z3]
  have z5 : f * e' = 0 := by rw [mul_comm, z2]
  have z6 : f * f = f := by rw [hf]; linear_combination h1 + h1' + 2 * h2
  simp only [Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, z1, z2, z3, z4, z5, z6, h1, h1', h2, zero_smul, add_zero, zero_add,
    Matrix.mul_assoc, g1, g2, Matrix.one_mul, Matrix.mul_one, hba, smul_add]
  rw [← Matrix.mul_assoc, hab', Matrix.smul_mul, smul_smul, h1', Matrix.one_mul, ← add_smul, ← add_smul,
    show e + e' + f = 1 by rw [hf]; ring, one_smul]

theorem reflectionBoost_matrix_conjTranspose_mul_self (e e' f : AE D) (a b : Mx D S.rank S.rank) (h1 : e * e = e) (h2 : e * e' = 0) (c1 : cA D e = e')
    (hf : f = 1 - e - e') (hba : b * a = e • (1 : Mx D S.rank S.rank)) :
    adj (e • a + e' • (giA S * (adj b * gA S)) + f • 1) * (gA S * (e • a + e' • (giA S * (adj b * gA S)) + f • 1)) = gA S := by
  have h1' : e' * e' = e' := by rw [← c1, ← RingHom.map_mul, h1]
  have hab' : adj a * adj b = e' • (1 : Mx D S.rank S.rank) := by rw [← adj_mul, hba, adj_smul, adj_one, c1]
  have hcc : cA D e' = e := by rw [← c1]; exact GlobalTheory.DualPairCheck.cA_cA _
  have cf : cA D f = f := by rw [hf, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, hcc, c1]; exact sub_right_comm _ _ _
  have q : adj (giA S * (adj b * gA S)) = gA S * b * giA S := by
    rw [adj_mul (giA S), adj_mul (adj b), adj_adj, adj_gA, adj_giA]
  have q2 : adj (e • a + e' • (giA S * (adj b * gA S)) + f • (1 : Mx D S.rank S.rank)) =
      e' • adj a + e • (gA S * b * giA S) + f • (1 : Mx D S.rank S.rank) := by
    rw [adj_add, adj_add, adj_smul e, adj_smul e', adj_smul f, q, hcc, cf, c1, adj_one (n := S.rank)]
  rw [q2]
  exact units_mul_relation_rearrange_commRing e e' f _ _ a _ b _ h1 h1' h2 hf hba hab' (giA_gA_cancel S) (gA_giA_cancel S)

end GlobalTheory.SplitHalf
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

def realPt (θ : InfFam D) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Classical.epsilon fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ

variable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)

def xiN (f : WO S T → ℂ) (z : VCx D.what₂.Tau a b) : ℂ :=
  Complex.exp ((Real.pi : ℂ) / 2 * HV sc z z) *
    f (realPt θ fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j)))

def toHom (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E) :=
  Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS))

def jetP (s : ℂ) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * jetC (fun _ => s) G (k.mapDomain fun v => (v.1, Fin.cast hT v.2.1, Fin.cast hS v.2.2))

def latFr (V : HSp D) {n : ℕ} (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin V.rank → D.host.E) :=
  {x | (fun i => x (Fin.cast hn.symm i)) ∈ N}

def Moves (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ x : Fin n → D.host.E, x ∈ N ↔ ∀ i, (finM V hn g⁻¹ *ᵥ fun j => eToEAf D (x j)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E

structure StdPair (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  sigS : S.SigOK
  sigT : T.SigOK
  rk : 0 < S.rank ∧ S.rank < T.rank ∧ Even S.rank ∧ Even T.rank
  cc : D.host.ccK = ⊤
  ne : δ ≠ 0
  xi : ∀ τ, tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ)
  scale : sc * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹

def IsHol (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f

def splitPart (V : HSp D) : Subgroup (GA D V) := Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ SuppAt e V g}

def IsRatFin (V : HSp D) (g : GA D V) : Prop := g ∈ GfC V ∧ ∃ γ ∈ GQ V, finHom V γ = finHom V g

end Gen

section World
variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m)

abbrev ColDat.xiS (f : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ :=
  xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc f

end World

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TrueColumnTupleTrivialEqOne
section
noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 NumberField IsDedekindDomain Matrix Formalism.UG

def LowerTie {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : Forms.FormsTiedSym D u Ch chOf) : Prop :=
  IsUnit (Forms.bZ u Tf.til.z0).det → ∀ (ψ : (D.mem u).P.Wz) (c : (D.fm u).clsP)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ),
    P ∈ Forms.CSpan ((D.fm u).lam D.R.m) →
    (∀ s, Tf.eWz ψ c s =
      Forms.fnOf _ (Forms.shiftOf (Forms.lamT u D.R.m)) (Forms.mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s)) →
    Tf.valP.eW ((D.mem u).P.lowerMap ψ) c = Forms.fnOf _ (Forms.shiftOf (Forms.sgT u)) 1 (Ker.brTen D u P)

def RootsG (D : D7) : Prop :=
  ∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

structure SelC (ex : Extra D L hT Gi Gl K Y cX) : Type 1 where

  host : Host.HostTied D

  real : Theta.RealTied D

  cols : Forms.ColsTiedSym D

  full : Forms.ColsFullS cols

  extra : Forms.ColsExtraTiedS full ex

  cf : Host.CharFrame D

  tp : Host.TupTied D cf ex.nch

  chrVal : Host.ValLL0 D cf

  chrDt : Host.DtTied D cf

  roots : RootsG D

  tw : Forms.SymmetricTwistedColumnsAtPrimes tp cols ex.tw

  emt : Rows.EMtTied D cols tw

  g : G.GroupCompatibilityAll D hT ex.cmp

  herm_eq : g.herm = full.1.to0

  forms_eq : g.forms = fun u => (cols.forms u).to0

  beOn : ∀ u, Ker.BeOnTie D u

  lower : ∀ u, LowerTie (cols.forms u)

  ambMetric : ∀ u, Rk.AmbMetric D u ex.amb

  ambLattice : ∀ u, Rk.AmbLattice D u ex.amb

structure SelB (ex : Extra D L hT Gi Gl K Y cX) : Type 1 extends SelC ex where

  ker : Ker.KerEntTied ex

  crd : ∀ (u : D.what₂.Word) i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E

  crd_gram : ∀ u i (hi : i ≤ D.R.m),
    cT (Forms.sigD D : D.host.E →+* D.host.E) (crd u i hi).1 * (crd u i hi).1 = Forms.gramN D i hi

  crd_lat : ∀ u i (hi : i ≤ D.R.m) (x : Fin (D.R.N i) → D.host.E),
    x ∈ Forms.selfDualLatticeCoords D i hi ↔ ∀ a, ((crd u i hi).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

  ker_sharp : ∀ μ, (ker.cst μ).sharp = true

  ker_frm : ∀ u μ i (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau),
    (ker.O u μ).frm i y τ = Forms.atInf (Forms.embT D) (crd u i hi).1 τ * (Forms.twYS tw.ch cols.forms u μ i hi y).1 τ

  aaUnit : ker.AAUnit

  unfAll : ker.UnfAll

  adapted : ker.Adapted

  top : ker.TopPinned

  chTie : ker.ChTie

  memSide : ker.MemSideU

  mtTw : ker.MtTwTie

  om : Formalism.L2.GlobalTheoryTheory.OmegaCompatible D ker.δ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {ex : Extra D L hT Gi Gl K Y cX}

end GlobalTheory.Core.Cls

end
end

