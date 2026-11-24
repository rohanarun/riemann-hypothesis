module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix

namespace GlobalTheory.GelfandKazhdan

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_comp {π : Representation ℂ G V} (φ : G →* G) (hφ : Function.Surjective φ)
    (h : π.IsIrreducible) : Representation.IsIrreducible (π.comp φ : Representation ℂ G V) := by
  let E : Subrepresentation (π.comp φ : Representation ℂ G V) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact U.apply_mem_toSubmodule g hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

variable [TopologicalSpace G]

theorem isAdmissible_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (h : IsAdmissible π) : IsAdmissible (π.comp φ : Representation ℂ G V) := by
  have e0 : (φ : G → G) = Φ := funext fun x => (hΦ x).symm
  have hc : Continuous φ := e0 ▸ Φ.continuous
  have ho : IsOpenMap φ := e0 ▸ Φ.isOpenMap
  refine ⟨fun v => (h.1 v).preimage hc, fun K hKo hKc => ?_⟩
  have e : fixed (π.comp φ : Representation ℂ G V) K = fixed π (K.map φ) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (ho _ hKo) (hKc.image hc)

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

theorem smoothTrace_comp {π : Representation ℂ G V} (φ : G →* G) (Φ : G ≃ₜ G) (hΦ : ∀ x, Φ x = φ x)
    (hμ : μ.map Φ = μ) (h : IsAdmissible π) {f : G → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) :
    smoothTrace (π.comp φ : Representation ℂ G V) μ (f ∘ Φ) = smoothTrace π μ f := by
  have h' := isAdmissible_comp φ Φ hΦ h
  unfold smoothTrace
  congr 1
  ext v
  refine eq_of_forall_dual fun l => ?_
  rw [h'.1.map_smoothOp (hf.comp_continuous Φ.continuous) (hc.comp_homeomorph Φ), h.1.map_smoothOp hf hc]
  conv_rhs => rw [← hμ]
  rw [Φ.measurableEmbedding.integral_map]
  simp [hΦ]

theorem smoothTrace_conj [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {π : Representation ℂ G V}
    (h : IsAdmissible π) {K : Subgroup G} (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (g : G) :
    smoothTrace π μ (fun x => f (g * x * g⁻¹)) = smoothTrace π μ f := by
  let Φ : G ≃ₜ G := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  let φ : G →* G := (MulAut.conj g).toMonoidHom
  have hΦ : ∀ x, Φ x = φ x := fun _ => rfl
  have hμ : μ.map Φ = μ :=
    ((measurePreserving_mul_right μ g⁻¹).comp (measurePreserving_mul_left μ g)).map_eq
  rw [← smoothTrace_comp φ Φ hΦ hμ h hf hc]
  refine (h.smoothTrace_eq_of_equiv (isAdmissible_comp φ Φ hΦ h).1 (hf.comp_continuous Φ.continuous)
    (hc.comp_homeomorph Φ) ho hK
    (LinearEquiv.ofLinear (π g) (π g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])) fun x v => ?_).symm
  change π g (π x v) = π (g * x * g⁻¹) (π g v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

end General

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion GlobalTheory.SplitFlip

theorem invTranspose_invTranspose (n : ℕ) (R : Type) [CommRing R] (g : GL (Fin n) R) :
    invTranspose n R (invTranspose n R g) = g :=
  Units.ext (transpose_transpose _)

theorem continuous_invTranspose (n : ℕ) (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invTranspose n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem equiv_contra (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (invTranspose n k)) (contra π)) := by
  borelize k
  letI : MeasurableSpace (GL (Fin n) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  have hb : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
    intro U hU
    obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
    exact ⟨J, h1, isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩
  let μ : Measure (GL (Fin n) k) := haarVol (KO k (Fin n))
  haveI : μ.IsHaarMeasure := isHaarMeasure_haarVol isOpen_KO le_rfl
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_haar μ
  have := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hinv := invTranspose_invTranspose n k
  have hcont := continuous_invTranspose n k
  let Ψ : GL (Fin n) k ≃ₜ* GL (Fin n) k :=
    { toFun := invTranspose n k, invFun := invTranspose n k, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul _, continuous_toFun := hcont, continuous_invFun := hcont }
  let Φ : GL (Fin n) k ≃ₜ GL (Fin n) k := Ψ.toHomeomorph
  have hΦ : ∀ x, Φ x = invTranspose n k x := fun _ => rfl
  have hμ : μ.map Φ = μ := by
    have : (μ.map Φ).IsHaarMeasure := Ψ.isHaarMeasure_map μ
    refine @eq_haarVol _ _ _ _ _ _ _ _ _ _ _ this _ isOpen_KO le_rfl ?_
    refine (Measure.map_apply (μ := μ) Φ.measurable isOpen_KO.measurableSet).trans ?_
    have e : Φ ⁻¹' (KO k (Fin n) : Set (GL (Fin n) k)) = KO k (Fin n) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_KO_iff]
      exact ⟨fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩, fun h => ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩⟩
    rw [e]
    exact haarVol_self isOpen_KO le_rfl
  obtain ⟨hca, hct⟩ := _root_.GlobalTheory.SmGL.ContraTrace.contra_admissible_trace _ μ hb V π ha
  let T : SB (GL (Fin n) k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => smoothTrace π μ φ.1
      map_add' := fun φ ψ => ha.smoothTrace_add φ.2.1 φ.2.2 ψ.2.1 ψ.2.2 isOpen_KO isCompact_KO
      map_smul' := fun c φ => ha.smoothTrace_smul φ.2.1 φ.2.2 isOpen_KO isCompact_KO c }
  have hT := GlobalTheory.T.transpose_invariant_of_conj_invariant_distribution_GL k (Fin n) T fun g φ ψ h => by
    change smoothTrace π μ ψ.1 = smoothTrace π μ φ.1
    rw [show ψ.1 = _ from funext h]
    exact smoothTrace_conj ha isOpen_KO isCompact_KO φ.2.1 φ.2.2 g
  refine _root_.GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq _ μ hb V _ _ _ (isAdmissible_comp _ Φ hΦ ha) hca
    (isIrreducible_comp _ (fun g => ⟨_, hinv g⟩) hi)
    ((_root_.GlobalTheory.ContraRefl.contra_irreducible_reflexive _ hb V V π π ha ha).1 hi) fun f hf hc => ?_
  have h1 := hf.comp_continuous Φ.continuous
  have h2 := hc.comp_homeomorph Φ
  have h3 := smoothTrace_comp _ Φ hΦ hμ ha h1 h2
  rw [show (f ∘ Φ) ∘ Φ = f from funext fun x => congrArg f (hinv x)] at h3
  rw [h3, hct f hf hc]
  refine hT ⟨fun g => f g⁻¹, hf.comp_continuous continuous_inv, hc.comp_homeomorph (Homeomorph.inv _)⟩
    ⟨f ∘ Φ, h1, h2⟩ fun x y hxy => congrArg f ?_
  rw [eq_inv_iff_mul_eq_one]
  apply Units.ext
  change (x⁻¹).valᵀ * y.val = 1
  rw [hxy, ← transpose_mul, Units.mul_inv, transpose_one]

end GlobalTheory.GelfandKazhdan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfIndexEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem exists_intertwiner_of_index_eq {D : D7} (hP : ItPair D) (k : Fin D.R.m) (hk : ChainPar D k)
    (V W : HSp D) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω f, IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  subst ha hb
  obtain ⟨It, -, hIt⟩ := hP k V W M M' θ ψ hθ hk
  exact ⟨It, hIt⟩

theorem innerIntertwiners_of_pair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hP : ItPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) :
    ItYSt R := by
  intro k hk
  have hk0 : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨It, hIt⟩ := exists_intertwiner_of_index_eq hP ⟨k, hk0⟩ (hC _) (Yc D k) (Yc D (k + 1))
    (min k D.R.m) (min (k + 1) D.R.m) (Nat.min_eq_left hk0.le) (Nat.min_eq_left hk.le)
    (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ
  refine ⟨It, fun t => ?_⟩
  obtain ⟨hω, hv⟩ := hS.1 t ⟨k, hk0⟩ hk
  exact hIt _ _ hω hv

end GlobalTheory.Chain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixMovedHomIntegralReduction
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRed

section General

variable {R k : Type} [CommRing R] [CommRing k] {b a : ℕ}


open Classical in
theorem int_mul (O : Subring R) (ρ : O →+* k) (z : Matrix (Fin b) (Fin b) O) (y : Matrix (Fin a) (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, (z.map O.subtype * N * y.map O.subtype) i j ∈ O) ∧
    (Matrix.of fun i j => if h : (z.map O.subtype * N * y.map O.subtype) i j ∈ O then
        ρ ⟨(z.map O.subtype * N * y.map O.subtype) i j, h⟩ else 0) =
      z.map ρ * (Matrix.of fun i j => if h : N i j ∈ O then ρ ⟨N i j, h⟩ else 0) * y.map ρ := by
  obtain ⟨M, rfl⟩ : ∃ M : Matrix (Fin b) (Fin a) O, N = M.map O.subtype :=
    ⟨Matrix.of fun i j => ⟨N i j, h i j⟩, by ext i j; rfl⟩
  have key : z.map O.subtype * M.map O.subtype * y.map O.subtype = (z * M * y).map O.subtype := by
    rw [Matrix.map_mul, Matrix.map_mul]
  have mem : ∀ i j, (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O := fun i j => by
    rw [key]; exact ((z * M * y) i j).2
  refine ⟨mem, ?_⟩
  have lhs : (Matrix.of fun i j => if h : (z.map O.subtype * M.map O.subtype * y.map O.subtype) i j ∈ O then
      ρ ⟨(z.map O.subtype * M.map O.subtype * y.map O.subtype) i j, h⟩ else 0) = (z * M * y).map ρ := by
    ext i j
    rw [Matrix.of_apply, dite_eq_left (mem i j), Matrix.map_apply]
    congr 1
    exact Subtype.ext (congrFun (congrFun key i) j)
  have mid : (Matrix.of fun i j => if h : M.map O.subtype i j ∈ O then ρ ⟨M.map O.subtype i j, h⟩ else 0) = M.map ρ := by
    ext i j
    rw [Matrix.of_apply, dite_eq_left (h i j)]
    rfl
  rw [lhs, mid, Matrix.map_mul, Matrix.map_mul]

theorem cancel (Z : GL (Fin b) R) (Y : GL (Fin a) R) (N : Matrix (Fin b) (Fin a) R) :
    Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val = N := by
  calc Z.val * ((Z⁻¹).val * N * Y.val) * (Y⁻¹).val
      = (Z.val * (Z⁻¹).val) * N * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem move {A : Type} [CommRing A] (f : A →+* R) (βS G Y : GL (Fin a) R) (βT H Z : GL (Fin b) R)
    (hY : βS * Y * βS⁻¹ = G) (hZ : βT * Z * βT⁻¹ = H)
    (g : Matrix (Fin a) (Fin a) A) (h : Matrix (Fin b) (Fin b) A) (hg : g.map f = G.val) (hh : h.map f = (H⁻¹).val)
    (x : Matrix (Fin b) (Fin a) A) :
    (βT⁻¹).val * (h * x * g).map f * βS.val = (Z⁻¹).val * ((βT⁻¹).val * x.map f * βS.val) * Y.val := by
  have eH : (H⁻¹).val = βT.val * ((Z⁻¹).val * (βT⁻¹).val) := by
    rw [← hZ, mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
  have eG : G.val = βS.val * (Y.val * (βS⁻¹).val) := by
    rw [← hY, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  rw [Matrix.map_mul, Matrix.map_mul, hg, hh, eH, eG]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc (βT⁻¹).val βT.val, Units.inv_mul, Matrix.one_mul]

private theorem bc_mul_restrict_mul_bc_eq (O : Subring R) (ρ : O →+* k) (z : GL (Fin b) O) (y : GL (Fin a) O)
    (N : Matrix (Fin b) (Fin a) R) (h : ∀ i j, N i j ∈ O) :
    (∀ i j, ((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O) ∧
    (Matrix.of fun i j => @dite _ (((Formalism.UG.bc O.subtype z).val * N * (Formalism.UG.bc O.subtype y).val) i j ∈ O)
        (Classical.propDecidable _) (fun h => ρ ⟨_, h⟩) (fun _ => 0)) =
      (Formalism.UG.bc ρ z).val *
        (Matrix.of fun i j => @dite _ (N i j ∈ O) (Classical.propDecidable _) (fun h => ρ ⟨N i j, h⟩) (fun _ => 0)) *
        (Formalism.UG.bc ρ y).val := by
  have ez : (Formalism.UG.bc O.subtype z).val = z.val.map O.subtype := rfl
  have ey : (Formalism.UG.bc O.subtype y).val = y.val.map O.subtype := rfl
  have ez' : (Formalism.UG.bc ρ z).val = z.val.map ρ := rfl
  have ey' : (Formalism.UG.bc ρ y).val = y.val.map ρ := rfl
  rw [ez, ey, ez', ey']
  exact GlobalTheory.FrameRed.int_mul O ρ z.val y.val N h

end General

variable {D : D7}

theorem isIntM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) :
    IsIntM (D := D) ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) ∧
    ∀ PP, redM (D := D) PP ((intGL D.host.F D.host.E b z).val * N * (intGL D.host.F D.host.E a y).val) =
      (Formalism.UG.bc (resS D.host.F PP) z).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  exact ⟨(bc_mul_restrict_mul_bc_eq _ (RingHom.id _) z y N h).1, fun PP => (bc_mul_restrict_mul_bc_eq _ (resS D.host.F PP) z y N h).2⟩

theorem mt_map (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (finE V g).val := rfl

theorem frMapO_actO {S T : HSp D} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {g : GA D S} {h : GA D T} {y : GL (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    {z : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : frGL βS y = finE S g) (hz : frGL βT z = finE T h) (x : WO S T) :
    frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) =
      ((intGL D.host.F D.host.E _ z)⁻¹).val * frMapO S T βS βT x * (intGL D.host.F D.host.E _ y).val := by
  have hY : βS * intGL D.host.F D.host.E _ y * βS⁻¹ = finE S g := by rw [← hy]; rfl
  have hZ : βT * intGL D.host.F D.host.E _ z * βT⁻¹ = finE T h := by rw [← hz]; rfl
  have hg : (Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) = (finE S g).val := by rw [inv_inv]; exact GlobalTheory.FrameRed.mt_map S g
  have hh : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((finE T h)⁻¹).val := by rw [GlobalTheory.FrameRed.mt_map, map_inv]
  show (βT⁻¹).val * (Formalism.L2.Theta.mt T h⁻¹ * x * Formalism.L2.Theta.mt S g⁻¹⁻¹).map (toEAf D) * βS.val = _
  exact GlobalTheory.FrameRed.move (toEAf D) βS (finE S g) (intGL D.host.F D.host.E _ y) βT (finE T h)
    (intGL D.host.F D.host.E _ z) hY hZ _ _ hg hh x

theorem isIntM_iff {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (N : Matrix (Fin b) (Fin a) (Datum.EAf D)) :
    IsIntM (D := D) (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) ↔
      IsIntM (D := D) N := by
  constructor
  · intro hM
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z y⁻¹ hM).1
    rwa [map_inv (intGL D.host.F D.host.E a) y, GlobalTheory.FrameRed.cancel] at h1
  · intro hN
    have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y hN).1
    rwa [map_inv (intGL D.host.F D.host.E b) z] at h1

theorem redM_mul {b a : ℕ} (z : GL (Fin b) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (y : GL (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E)) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)}
    (h : IsIntM (D := D) N) (PP : Pl D.host.E) :
    redM (D := D) PP (((intGL D.host.F D.host.E b z)⁻¹).val * N * (intGL D.host.F D.host.E a y).val) =
      ((Formalism.UG.bc (resS D.host.F PP) z)⁻¹).val * redM (D := D) PP N * (Formalism.UG.bc (resS D.host.F PP) y).val := by
  have h1 := (GlobalTheory.FrameRed.isIntM_mul (D := D) z⁻¹ y h).2 PP
  rwa [map_inv (intGL D.host.F D.host.E b) z, map_inv (Formalism.UG.bc (resS D.host.F PP)) z] at h1

theorem frMapO_actO_red : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ x : WO S T, (IsIntM (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) ↔ IsIntM (frMapO S T βS βT x)) ∧ (IsIntM (frMapO S T βS βT x) → ∀ PP, redM PP (frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)) = ((redFn βT PP (finE T h))⁻¹).val * redM PP (frMapO S T βS βT x) * (redFn βS PP (finE S g)).val) := by
  intro D S T βS βT g h hg hh x
  unfold St at hg hh
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hg
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hh
  have e := GlobalTheory.FrameRed.frMapO_actO hy hz x
  refine ⟨?_, fun hI PP => ?_⟩
  · rw [e]
    exact GlobalTheory.FrameRed.isIntM_iff z y _
  · rw [e, GlobalTheory.FrameRed.redM_mul z y hI PP]
    have a : redFn βS PP (finE S g) = Formalism.UG.bc (resS D.host.F PP) y := by
      rw [← hy]; exact redFn_frGL βS PP y
    have b : redFn βT PP (finE T h) = Formalism.UG.bc (resS D.host.F PP) z := by
      rw [← hz]; exact redFn_frGL βT PP z
    rw [a, b]

end GlobalTheory.FrameRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IoYStOfIoPair
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain

theorem IoPair.of_index_eq {D : D7} (hP : IoPair D) (k : Fin D.R.m) (a b : ℕ) (ha : a = k) (hb : b = k + 1)
    (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (hθ : IsInfFam θ) (hC : ChainPar D k)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (hW : IsStepWeil k ψ V W ω) (hV : IsVacVec ψ θ M M' f)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hI : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (hJ : ∀ κ ∈ J, κ ∈ GfC V ∧ ω (κ, 1) f = χ κ • f)
    (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (hν : ν.IsHaarMeasure)
    (h𝓕 : MeasureTheory.IsFundamentalDomain (GQ W) 𝓕 ν)
    (J' : Set (GA D W)) (χ' : GA D W → ℂ) (C : Submodule ℂ (SmT M' →ₗ[ℂ] (GA D W → ℂ)))
    (hle : C ≤ MultT θ M' J' χ') :
    Lift.IoExists ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f) It C (MultT θ M J χ) := by
  subst ha hb
  exact hP k V W M M' θ ψ hθ hC ω f hW hV It hI J χ hJ ν 𝓕 hν h𝓕 J' χ' C hle

theorem ioYSt_of_ioPair (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : StepsOK R) (hL : LawsOK R)
    (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hkm : k < D.R.m := Nat.lt_of_succ_lt hk
  have hIt := hI
  have hInner := hν
  have hLast := hν'
  unfold RealDat.chain_ItY at hIt
  unfold RealDat.models_νY at hInner
  unfold RealDat.models_νY' at hLast

  have hmeas : (R.νY t (k + 1)).IsHaarMeasure ∧
      MeasureTheory.IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · exact ⟨(hInner t (k + 1) h2).1.1, (hInner t (k + 1) h2).2⟩
    · have atLast : ∀ j, j = D.R.m - 1 → (R.νY t j).IsHaarMeasure ∧
          MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
        rintro j rfl
        exact ⟨(hLast t).1.1, (hLast t).2⟩
      exact atLast (k + 1) (by omega)
  obtain ⟨hW, hV⟩ := hS.1 t ⟨k, hkm⟩ hk
  exact IoPair.of_index_eq hP ⟨k, hkm⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hkm.le)
    (min_eq_left hk.le) (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k)
    (R.vY t k) hW hV (R.ItY k) (hIt t k hk) _ _ (hL.1 t k hk) (R.νY t (k + 1)) (R.fdY t (k + 1))
    hmeas.1 hmeas.2 _ _ (R.CC t (k + 1)) le_rfl

end GlobalTheory.Chain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteFock

variable {D : D7}

theorem compAt_mt_of_finite (θ : InfFam D) (τ : D.what₂.Tau) {S : HSp D} {k : GA D S} (hk : k ∈ GfC S) :
    compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
  have h1 : (Formalism.L2.Theta.mt S k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt S k) = ((Formalism.L2.Theta.mt S k).map (infPart D)).map (θ τ) := rfl
  rw [h2, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem dRho_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [Pi.smul_apply, smul_eq_mul, ← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT) (c : ℂ)
    (f : WO S T → ℂ) (P) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, Module.End.one_apply]
  rw [dRho_smul, dRho_smul, smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem pureTensorO_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT)
    (f : WO S T → ℂ) : pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have e : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  unfold pureTensorO pureTensorL
  rw [e, Module.Basis.constr_basis]
  simp [opPow]

theorem om_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT f, (∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)) → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, ∀ c : ℂ, om (k, k') f = c • f → ∀ P, om (k, k') (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  intro D ψ θ S T χS χT om hθ hom sS sT BS BT f hf k hk k' hk' c hc P
  have hf0 : IsThetaFunO ψ S T f := by simpa only [pureTensorO_one] using hf 1
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k k'
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.one_mul]) f hf0 P).2, hc, pureTensorO_smul]

end GlobalTheory.FiniteFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

theorem div_or_isConjPl_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D P k PP h
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D P k PP h with h1 | ⟨w, h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨w, h1, fun c hc => ⟨Formalism.L2.Col.cO D.host.E c, ?_, rfl⟩⟩
    rw [h2, Formalism.L2.Col.conjIdeal_eq] at hc
    exact hc

end GlobalTheory.StepLaw
end

