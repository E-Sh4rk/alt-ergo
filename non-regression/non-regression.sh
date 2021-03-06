echo "===============================================================================================";
echo "[ with Tableaux ]"
echo "===============================================================================================";
./main_script.sh "-sat-solver Tableaux"

echo "===============================================================================================";
echo "[ with CDCL-Tableaux ]"
echo "===============================================================================================";
./main_script.sh "-sat-solver CDCL-Tableaux"

echo "===============================================================================================";
echo "[ with CDCL ]"
echo "===============================================================================================";
./main_script.sh "-sat-solver CDCL"

echo "===============================================================================================";
echo "[ with Tableaux-CDCL ]"
echo "===============================================================================================";
./main_script.sh "-sat-solver Tableaux-CDCL"

echo "===============================================================================================\c";
echo "===============================================================================================";
echo "[ WITH FM-SIMPLEX ]"
echo "===============================================================================================\c";
echo "===============================================================================================";
./main_script.sh "-inequalities-plugin `pwd`/../sources/fm-simplex-plugin.cmxs"
