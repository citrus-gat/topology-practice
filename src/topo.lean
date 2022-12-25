import topology.basic
import topology.metric_space.basic 


-- Open balls in an ultrametric space are closed 
example {X : Type*}[metric_space X] (x : X) (r : ℝ) (r_pos : r > 0) (strong_ti : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z)) : 
is_closed (metric.ball x r /-B(x, r)-/ ) := 
begin 
  rw ← is_open_compl_iff,
  rw metric.is_open_iff,
  intros y y_not_in, 
  change ¬ dist y x < r at y_not_in,
  -- have : dist y x ≥ r := by linarith,
  -- replace_hyp y_not_in (dist y x ≥ r) (by linarith),
  use [r, r_pos],
  intros z hz,
  change ¬ dist z x < r,
  change dist z y < r at hz,
  by_contradiction H,
  -- suffices : dist y x < r, { from y_not_in this, },
  have : dist y x < r :=
    calc dist y x ≤ max (dist y z) (dist z x) : strong_ti _ _ _
              ... = max (dist z y) (dist z x) : by rw dist_comm y z
              ... < r : max_lt hz H, 
  exact y_not_in this,
end

-- Closed balls in an ultrametric space are open
example {X : Type*}[metric_space X] (x : X) (r : ℝ) (r_pos : r > 0) (strong_ti : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z) ): 
is_open (metric.closed_ball x r) := 
begin 
  rw metric.is_open_iff,
  intros y y_in,
  use [r, r_pos],
  intros z z_in,
  -- change dist y x ≤ r at y_in,
  -- change dist z y < r at z_in,
  have : dist z y ≤ r := le_of_lt z_in,
  calc dist z x ≤ max (dist z y) (dist y x) : strong_ti _ _ _ 
            ... ≤ r : max_le this y_in,
end 


-- If X Y are topological spaces, Y is Hausdorff, f and g are continuous functions from X to Y, 
-- then the set {x ∈ X : f x = g x} is closed. 
example {X Y : Type*}[topological_space X][topological_space Y][t2_space Y]{f g : X → Y} :
continuous f → continuous g → is_closed {x : X | f x = g x} := 
begin 
  intros hfcts hgcts,
  suffices : is_open {x : X | f x ≠ g x}, { rwa ← is_open_compl_iff },
  rw is_open_iff_forall_mem_open,
  intros x x_in,
  rcases t2_separation (x_in) with ⟨U, V, U_open, V_open, fx_in_U, gx_in_V, UdisjV⟩,
  use (f ⁻¹' U) ∩ (g ⁻¹' V),
  repeat {split},
  { -- (f ⁻¹' U) ∩ (g ⁻¹' V) is contained in the set {x : X | f x ≠ g x}
    intros x' x'_in, 
    rw set.mem_inter_iff at x'_in,
    repeat {rw set.mem_preimage at x'_in},
    exact disjoint.ne_of_mem UdisjV x'_in.left x'_in.right },
  { -- (f ⁻¹' U) ∩ (g ⁻¹' V) is open
    exact is_open.inter (is_open.preimage hfcts U_open) (is_open.preimage hgcts V_open) }, 
    -- x ∈ f⁻¹(U) and x ∈ f⁻¹(V)
  repeat { rwa set.mem_preimage },
end
