<?php

$pages = array('Home', 'Team', 'Results', 'Documentation');

if (isset ($_GET['page'])) { $page = (int) $_GET['page']; }
else { $page=0; }

include('top.inc.php');

if ($page == 0)
{

?>
<h2>Origin &amp; Objectives</h2>

<p>The <a href="https://sourceforge.net/projects/coqtail/">COQTAIL</a> project is the biological
son of the workpackage `Proofs` of the <a href="http://graal.ens-lyon.fr/coquille">COQUILLE</a> 
project. It is therefore based on all the results obtained during the development of COQUILLE.</p>

<p>In addition to implementing tools dedicated to the easy formalization of mathematics as we see 
them in french <i>Classes préparatoires</i>, this project will proove licence-level results.</p> 

<h2>Development axis</h2>

<ul>
	<li>Analysis (real and complex)</li>
	<li>Arithmetic</li>
	<li>Calculability</li>
	<li><b>C</b> implementation</li>
	<li>Logic and <b>R</b> axiomatic expressivity</li>
	<li>Topology</li>
</ul>
<?php

}

elseif($page == 1)
{

?>
<ul>
	<li><a href="http://sourceforge.net/project/memberlist.php?group_id=298939">Team</a></li>
	<li><a href="http://graal.ens-lyon.fr/coquille/index.php?page=team">Former team</a> (COQUILLE project)</li>
</ul>
<?php

}

elseif($page == 2)
{

?>
<h2>A bunch of nice results</h2>
<ul>
	<li>The uncountability of <b>R</b></li>
	<li>The reals axioms imply Markov principle</li>
	<li>Zeta(2)'s value is pi²/6</li>
</ul>

<h2>New libraries</h2>

<ul>
	<li>Arithmetic</li>
	<li>Topology (Various typeclasses definitions)</li>
	<li>Clean libraries on sequences of reals or complexes</li>
   <li>Complexes' definition and collection of basic results</li>
   <li>Formalization of power series and their convergence radius</li>
</ul>
<?php

}

elseif($page == 3)
{

?>
<a href="http://graal.ens-lyon.fr/coquille/coqdoc/">COQUILLE's project documentation</a>
<?php
}
include('foot_en.inc.php')
?>
