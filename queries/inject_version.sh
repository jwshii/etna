dir=$1

# Use find with a while loop to safely handle filenames with spaces
find "$dir" -name '*.json' | while IFS= read -r file; do
  # Split filename into parts using a comma as the delimiter
  parts=(${file//,/ })

  # Check if the array has at least 5 elements
  if [ ${#parts[@]} -ge 5 ]; then
    # Slice the array to get the version (elements from index 4 onwards)
    version="${parts[@]:4}"
    
    # Join the version array back into a string, separated by commas
    version=$(printf "%s," "${parts[@]:4}")
    
    # Remove the trailing comma
    version="${version%,}"
    
    # Run jq command with the version argument
    echo "Injecting version $version into $file"
    jq --raw-output --arg version "$version" -f 'queries/inject_version.jq' "$file" > "$file.tmp" && mv "$file.tmp" "$file"
  else
    echo "Skipping $file"
  fi
done
